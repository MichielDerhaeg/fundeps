{-# LANGUAGE LambdaCase #-}

module Frontend.HsTypeChecker where

import           Frontend.FunDep
import           Frontend.HsRenamer
import           Frontend.HsTypes
import           Frontend.TcConditions
import           Frontend.TcEntail
import           Frontend.TcGen
import           Frontend.TcMonad
import           Frontend.TcType

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.AssocList
import           Utils.Ctx
import           Utils.Errors
import           Utils.FreeVars
import           Utils.Kind
import           Utils.PrettyPrint
import           Utils.Substitution
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Arrow        (first)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List            (nub, (\\))
import           Data.Semigroup

-- * Create the typechecking environment from the renaming one
-- ------------------------------------------------------------------------------

-- | Build the initial typechecker environment from the renaming environment
buildInitTcEnv :: RnProgram -> RnEnv -> TcM ()
buildInitTcEnv pgm (RnEnv _rn_cls_infos dc_infos tc_infos) = do
  -- Prepopulate the environment with the (user-defined) data constructor information
  mapAssocListM_ (uncurry addDataConInfoTcM) $
    mapFstWithDataAssocList (\_ info -> hs_dc_data_con info) dc_infos
  -- Prepopulate the environment with the (user-defined) type constructor information
  mapAssocListM_ (uncurry addTyConInfoTcM)   $
    mapFstWithDataAssocList (\_ info -> hs_tc_ty_con   info) tc_infos
  -- Create and store in the environment all infos for type classes
  buildStoreClsInfos pgm
  where
    buildStoreClsInfos :: RnProgram -> TcM ()
    buildStoreClsInfos (Program decls) = mapM_ go decls
      where
        go (ClsDecl (ClsD rn_abs rn_cs rn_cls rn_as rn_fundeps rn_method method_ty)) = do
          -- Generate And Store The TyCon Info
          fc_tc <-
            FcTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls))) <$> getUniqueM

          -- Generate And Store The DataCon Info
          fc_dc  <-
            FcDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls))) <$> getUniqueM

          fd_fams <- forM (zip [0..] rn_fundeps) $ \(i,Fundep ais ai0) -> do
            fd_fam <- HsTF .
              mkName (mkSym ("FunDep" ++ show (symOf rn_cls) ++ show (i :: Word)))
              <$> getUniqueM
            addTyFamInfoTcM fd_fam $ HsTFInfo fd_fam ais (kindOf ai0)
            return fd_fam

          -- Generate And Store The Class Info
          let cls_info =
                ClassInfo
                  (labelOf rn_abs \\ rn_as)
                  rn_cs
                  rn_cls
                  rn_as
                  rn_fundeps
                  fd_fams
                  rn_method
                  method_ty
                  fc_tc
                  fc_dc
          addClsInfoTcM rn_cls cls_info
        go _ = return ()


-- * Class Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl :: RnClsDecl -> TcM ([FcDecl], TcCtx)
elabClsDecl (ClsD ab_s rn_cs cls as fundeps method method_ty) = do
  tc <- lookupClsTyCon   cls
  dc <- lookupClsDataCon cls

  let bs    = labelOf ab_s \\ as
  let fc_as = rnTyVarToFcTyVar <$> as
  let fc_bs = rnTyVarToFcTyVar <$> bs

  unambiguousCheck bs as rn_cs

  -- Elaborate the superclass constraints (with full well-formedness checking also)
  fc_sc_tys <- extendCtxM (labelOf ab_s) (dropLabel ab_s) (mapM wfElabClsCt rn_cs)

  -- Elaborate the method type (with full well-formedness checking also)
  (_kind, fc_method_ty) <- extendCtxM as (kindOf <$> as) (wfElabPolyTy method_ty)

  fs <- lookupClsFDFams cls
  let (fc_props, fc_fam_decls) = unzip $
        map
          (\(f, Fundep ais ai0) ->
             ( FcProp
                 (FcTyFam (rnTyFamToFcFam f) (rnTyVarsToFcTypes ais))
                 (rnTyVarToFcType ai0)
             , FcFamDecl (rnTyFamToFcFam f) (rnTyVarToFcTyVar <$> ais) (kindOf ai0)))
          (zipExact fs fundeps)

  -- Generate the datatype declaration
  let fc_data_decl =
        FcDataDecl
          tc
          fc_as
          [(dc, fc_bs, fc_props, fc_sc_tys ++ [fc_method_ty])]

  -- Generate the method implementation
  (fc_val_bind, hs_method_ty) <- do
    let (as', cs', ty') = destructPolyTy method_ty
    let (real_as, real_cs) = (as <> labelOf as', ClsCt cls (TyVar <$> as):cs')

    -- Source and target method types
    let real_method_ty =
          constructPolyTy
            ( zipWithExact (:|) real_as (kindOf <$> real_as)
            , real_cs
            , ty')
    (_kind, full_fc_method_ty) <- wfElabPolyTy real_method_ty

    -- n superclass variables + 1 for the method
    xs <- replicateM (length rn_cs +1) freshFcTmVar

    -- Annotate the constraints with fresh dictionary variables
    (ds, ann_cs) <- annotateClsCs real_cs
    -- elaborate the annotated dictionary variables to System F term binders
    dbinds <- elabAnnClsCs ann_cs

    let fc_as' = map rnTyVarToFcType $ labelOf <$> as'

    -- Elaborate the dictionary types
    fc_cs_tys <- mapM elabClsCt rn_cs

    -- Elaborate the type of the dictionary contained method
    dict_method_ty <- elabPolyTy method_ty

    co_vars <- mapM (const freshFcCoVar) fc_props

    let fc_method_rhs =
          fcTmTyAbs (rnTyVarToFcTyVar <$> real_as) $
          fcTmAbs dbinds $
          FcTmCase
            (FcTmVar (head ds))
            [ FcAlt
                (FcConPat
                   dc
                   (rnTyVarToFcTyVar <$> bs)
                   (co_vars |: fc_props)
                   (xs |: (fc_cs_tys ++ [dict_method_ty])))
                (fcDictApp (fcTmTyApp (FcTmVar (last xs)) fc_as') (tail ds))
            ]

    let fc_val_bind = FcValBind (rnTmVarToFcTmVar method) full_fc_method_ty fc_method_rhs

    return (fc_val_bind, real_method_ty)

  -- Construct the extended typing environment
  ty_ctx <- extendCtxM method hs_method_ty ask

  -- TODO wtf is this
  return (fc_fam_decls <> [fc_data_decl, fc_val_bind], ty_ctx)

-- | Elaborate a list of annotated dictionary variables to a list of System F term binders.
elabAnnClsCs :: AnnClsCs -> TcM [(FcTmVar, FcType)]
elabAnnClsCs = mapM (\(d :| ct) -> (,) d <$> elabClsCt ct)

-- * Data Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a datatype declaration
elabDataDecl :: RnDataDecl -> TcM [FcDecl]
elabDataDecl (DataD tc as dcs) = do
  -- Elaborate the type constructor
  fc_tc <- hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc
  -- Elaborate the universal type variables
  let fc_as = map (rnTyVarToFcTyVar . labelOf) as

  decls <- elabProjections tc as

  fc_dcs <- forM dcs $ \(dc, tys) -> do
    -- Elaborate the data constructor
    fc_dc <- hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc
    -- Elaborate the argument types
    (kinds, fc_tys) <- unzip <$> extendCtxKindAnnotatedTysM as (mapM wfElabMonoTy tys)
    unless (all (==KStar) kinds) $
      tcFail (text "elabDataDecl" <+> colon <+> text "not all datacon args have kind star")
    return (fc_dc, mempty, mempty, fc_tys)
  return $ [FcDataDecl fc_tc fc_as fc_dcs] <> decls

-- | Elaborate the projection type functions of the type constructor
elabProjections :: RnTyCon -> [RnTyVarWithKind] -> TcM [FcDecl]
elabProjections tc as = do
  proj_fams <- lookupTyConProj tc
  fmap concat $ forM (zip proj_fams as) $ \(proj_fam, a) -> do
    addTyFamInfoTcM proj_fam (HsTFInfo proj_fam (labelOf as) (dropLabel a))
    g <- freshFcAxVar
    a' <- freshFcTyVar KStar
    let fc_fam = rnTyFamToFcFam proj_fam
    let axiom =
          Axiom
            g
            (labelOf as)
            proj_fam
            [mkTyConApp tc (TyVar <$> (labelOf as))]
            (TyVar (labelOf a))
    tExtendAxiomsM [axiom]
    return
      [ FcFamDecl
         fc_fam
         [a']
         (dropLabel a)
      , elabAxiom axiom ]

-- | Extend the typing environment with some kind annotated type variables
extendCtxKindAnnotatedTysM :: [RnTyVarWithKind] -> TcM a -> TcM a
extendCtxKindAnnotatedTysM ann_as = extendCtxM as (map kindOf as)
  where
    as = map labelOf ann_as

-- * Class Instance Elaboration
-- ------------------------------------------------------------------------------

elabInsDecl :: RnInsDecl -> TcM [FcDecl]
elabInsDecl (InsD ab_s ins_cs cls tys method method_tm) = do
  let head_ct = ClsCt cls tys
  let as = ftyvsOf tys
  let bs = labelOf ab_s \\ as
  let fc_abs = rnTyVarToFcTyVar . labelOf <$> ab_s
  theory <- getGlobalTheory

  overlapCheck theory head_ct
  unambiguousCheck bs as ins_cs

  ins_d <- freshDictVar
  ins_scheme <- freshenLclBndrs $ CtrScheme ab_s ins_cs head_ct
  checkCompat theory ins_scheme
  termCheckInstance ins_scheme
  checkUnambWitness ins_scheme

  ann_ins_cs <- snd <$> annotateClsCs ins_cs

  (mctx, match_cs, match_ctx) <- dictDestruction ann_ins_cs

  axioms <- generateAxioms ins_scheme
  unless (all (termCheckAxiom) axioms) $
    throwErrorM $
    text "The instance declaration does not satisfy the termination conditions"
    <> colon $$ ppr ins_scheme

  let i_theory = theory `tExtendAxioms`   axioms
                        `tExtendGivenCls` ann_ins_cs
                        `tExtendGivens`   match_cs

  (fc_exis_tys, fc_cos, fc_tms) <- entailSuperClass (labelOf ab_s) i_theory head_ct

  tExtendAxiomsM axioms
  tExtendSchemesM [ins_d :| ins_scheme]

  fc_method_tm <- do
    let theory' = i_theory `tExtendSchemes` [ins_d :| ins_scheme]
    expected_method_ty <- instMethodTy tys <$> lookupCtxM method
    setCtxM match_ctx $ extendCtxM (labelOf ab_s) (dropLabel ab_s) $
      elabTermWithSig (labelOf ab_s) theory' method_tm expected_method_ty

  dtrans_ty <- extendCtxM (labelOf ab_s) (dropLabel ab_s) $ do
    fc_head_ty <-  wfElabClsCt head_ct
    fc_ins_cs <- wfElabClsCs ins_cs
    return $ fcTyAbs fc_abs $ fcTyArr fc_ins_cs fc_head_ty

  fc_dict_transformer <- do
    binds <- elabAnnClsCs ann_ins_cs
    dc    <- lookupClsDataCon cls
    return $
      fcTmTyAbs fc_abs $
       fcTmAbs binds $
         matchCtxApply mctx $
          FcTmDataCon dc `fcTmTyApp` (elabMonoTy <$> tys)
                         `fcTmTyApp` fc_exis_tys
                         `fcTmCoApp` fc_cos
                         `fcTmApp`   fc_tms
                         `FcTmApp`   fc_method_tm

  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer
  return ((elabAxiom <$> axioms) <> [fc_val_bind])

entailSuperClass :: [RnTyVar] -> Theory -> RnClsCt -> TcM ([FcType], [FcCoercion], [FcTerm])
entailSuperClass untchs theory (ClsCt cls tys) = do
  ClassInfo bs sc _cls as fds fams _m _mty _tc _dc <-
    lookupTcEnvM tc_env_cls_info cls
  subst <- mappend (buildSubst (zipExact as tys)) <$> determinacy as sc
  cs <- genFreshCoVars $ length fds
  let eq_cs = substInAnnEqCs subst $ cs |:
        map
          (\(Fundep ais ai0, f) -> (TyFam f (TyVar <$> ais)) :~: TyVar ai0)
          (zipExact fds fams)
  (ds, cls_cs) <- annotateClsCs $ substInClsCs subst sc
  let general_cs = (WantedEqCt <$> eq_cs) <> (WantedClsCt <$> cls_cs)
  (residual_cs, ty_subst, ev_subst) <- entail untchs theory general_cs
  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve super class constraints" <+> colon <+> ppr residual_cs
       $$ text "From" <+> colon <+>
       ppr theory $$ text "Constraints" <+> colon <+> ppr general_cs)
  return
    ( elabMonoTy . substInMonoTy (ty_subst <> subst) . TyVar <$> bs
    , substEvInCo ev_subst . FcCoVar <$> cs
    , substEvInTm ev_subst . FcTmVar <$> ds)

dictDestruction :: AnnClsCs -> TcM (MatchCtx, GivenCs, TcCtx)
dictDestruction [] = (,,) MCtxHole mempty <$> ask
dictDestruction ((d :| ClsCt cls tys):cs) = do
  ClassInfo bs sc _cls as fds fams _m mty _tc dc <-
    lookupTcEnvM tc_env_cls_info cls

  (bs', bs_subst) <- freshenRnTyVars bs
  let subst = bs_subst <> (buildSubst $ zipExact as tys)

  cvs <- genFreshCoVars $ length fds
  let eq_cs =
        substInEqCs subst $
        map
          (\(fam, Fundep ais ai0) -> TyFam fam (TyVar <$> ais) :~: TyVar ai0)
          (zipExact fams fds)
  let given_eq_cs = GivenEqCt <$> ((FcCoVar <$> cvs) |: eq_cs)

  let fc_props = elabEqCt <$> eq_cs

  ds <- genFreshDictVars $ length sc
  fc_tys <- elabClsCs $ substInClsCs subst sc

  f <- freshRnTmVar
  let subbed_mty = substInPolyTy subst mty
  fc_mty <- elabPolyTy subbed_mty

  let new_cs = ds |: substInClsCs subst sc
  env <- extendCtxM f subbed_mty $ extendCtxM (bs) (kindOf <$> bs) ask
  (mctx, new_cs', env') <- setCtxM env $ dictDestruction $ new_cs ++ cs

  let given_cls_cs = GivenClsCt <$> ((FcTmVar <$> ds) |: substInClsCs subst sc)

  let pat =
        FcConPat
          dc
          (rnTyVarToFcTyVar <$> bs')
          (cvs |: fc_props)
          (ds  |: fc_tys ++ [rnTmVarToFcTmVar f :| fc_mty])
  return (MCtxCase d pat mctx, given_eq_cs <> given_cls_cs <> new_cs', env')

generateAxioms :: CtrScheme -> TcM Axioms
generateAxioms scheme@(CtrScheme _as cs ct) = do
  inst_fds <- instantiateFDs ct
  forM (inst_fds) $ \(f, uis, ui0) -> do
    let free_uis = ftyvsOf uis
    subst <- determinacy free_uis cs
    let subbed_ui0 = substInMonoTy subst ui0
    unless (null (ftyvsOf subbed_ui0 \\ free_uis)) gen_ax_fail
    g <- freshFcAxVar
    return $ Axiom g free_uis f uis subbed_ui0
  where
    gen_ax_fail =
      tcFail $
      text "Liberal Coverage Condition violation by the constraint scheme" <+>
      colon <+> ppr scheme

-- | Instantiate a method type for a particular instance
instMethodTy :: [RnMonoTy] -> RnPolyTy -> RnPolyTy
instMethodTy typats poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    (as,_ct:cs,ty) = destructPolyTy poly_ty
    subst  = buildSubst $ zip (labelOf as) typats
    new_as = drop (length typats) as
    new_cs = substInClsCs  subst cs
    new_ty = substInMonoTy subst ty

-- | Elaborate a term with an explicit type signature (method implementation).
-- This involves both inference and type subsumption.
elabTermWithSig :: [RnTyVar] -> Theory -> RnTerm -> RnPolyTy -> TcM FcTerm
elabTermWithSig untchs theory tm poly_ty = do
  let (as, cs, ty2) = destructPolyTy poly_ty

  ((ty1, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  c <- freshFcCoVar
  given_ccs <- snd <$> annotateClsCs cs

  (mctx, match_ccs, _) <- dictDestruction given_ccs

  let theory' = theory `tExtendGivens`  match_ccs
                       `tExtendGivenCls` given_ccs
  let untouchables = untchs <> labelOf as

  (residual_cs, ty_subst, ev_subst) <- entail untouchables theory' $
    (WantedClsCt <$> wanted_ccs) <>
    (WantedEqCt <$> wanted_eqs <> [c :| ty1 :~: ty2])

  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve constraints" <+>
       colon <+>
       ppr residual_cs $$ text "From" <+>
       colon <+> ppr theory' $$ text "Wanted" <+> colon <+> ppr wanted_ccs)

  dbinds <- elabAnnClsCs given_ccs
  let fc_ty_subst = elabHsTySubst ty_subst
  return $
    fcTmTyAbs (rnTyVarToFcTyVar <$> (labelOf as)) $
    fcTmAbs dbinds $
    matchCtxApply mctx $
    substFcTyInTm fc_ty_subst $
    substEvInTm ev_subst $ FcTmCast fc_tm (FcCoVar c)

annClsCsToGivenCs :: AnnClsCs -> GivenCs
annClsCsToGivenCs ann_cs =
  GivenClsCt <$> ((FcTmVar <$> labelOf ann_cs) |: dropLabel ann_cs)

-- * Type Inference Without Signature
-- ------------------------------------------------------------------------------

elabTermSimpl :: Theory -> RnTerm -> TcM (RnPolyTy, FcTerm)
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  (_, eq_ty_subst, eq_ev_subst) <-
    entail mempty theory (WantedEqCt <$> wanted_eqs)

  let refined_ccs = substInAnnClsCs eq_ty_subst wanted_ccs
  let refined_monoty = substInMonoTy eq_ty_subst mono_ty

  let untchs = nub $ ftyvsOf refined_monoty <> ftyvsOf refined_ccs

  (residual_cs, cls_ty_subst, cls_ev_subst) <-
    entail untchs theory (WantedClsCt <$> refined_ccs)

  let ty_subst = eq_ty_subst <> cls_ty_subst
  let ev_subst = eq_ev_subst <> cls_ev_subst

  -- Generalize the type
  let new_mono_ty = substInMonoTy cls_ty_subst refined_monoty
  let new_cs      = map dropLabel residual_cs
  let new_as      = nub $ ftyvsOf new_mono_ty <> ftyvsOf residual_cs
  let gen_ty      = constructPolyTy ( new_as |: (kindOf <$> new_as)
                                    , new_cs
                                    , new_mono_ty
                                    )

  -- Elaborate the term
  let fc_as = map rnTyVarToFcTyVar new_as
  dbinds   <- elabAnnClsCs residual_cs
  let full_fc_tm = fcTmTyAbs fc_as $
                     fcTmAbs dbinds $
                       substFcTyInTm (elabHsTySubst ty_subst) $
                         substEvInTm ev_subst
                          fc_tm

  return (gen_ty, full_fc_tm)

-- * Value Binding Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a top-level value binding
elabValBind :: RnValBind -> TcM (FcDecl, TcCtx)
elabValBind (ValBind a m_ty tm) = do
  theory <- getGlobalTheory
  (ty,fc_tm) <- case m_ty of
    Nothing -> elabTermSimpl theory tm
    Just ty -> do
      fc_tm <- extendCtxM a ty $ elabTermWithSig mempty theory tm ty
      return (ty,fc_tm)
  ctx <- ask
  fc_ty <- elabPolyTy ty
  let fc_val_bind = FcValBind (rnTmVarToFcTmVar a) fc_ty fc_tm
  return (fc_val_bind, extendCtx ctx a ty)

-- * Program Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a declaration
elabDecl :: RnDecl -> TcM ([FcDecl], TcCtx)
elabDecl (ClsDecl decl)  = elabClsDecl decl
elabDecl (InsDecl decl)  = (,) <$> elabInsDecl decl <*> ask
elabDecl (DataDecl decl) = (,) <$> elabDataDecl decl <*> ask
elabDecl (ValDecl decl)  = first (pure) <$> elabValBind decl

-- | Elaborate a program
elabProgram :: RnProgram -> TcM FcProgram
elabProgram (Program pgm_decls) = FcProgram <$> go pgm_decls
  where
    go :: [RnDecl] -> TcM [FcDecl]
    go (decl:decls)= do
      (fc_decls, ext_ty_env) <- elabDecl decl
      more_fc_decls <- setCtxM ext_ty_env $ go decls
      return (fc_decls <> more_fc_decls)
    go [] = return []

-- * Invoke the complete type checker
-- ------------------------------------------------------------------------------

hsElaborate ::
     RnEnv
  -> UniqueSupply
  -> RnProgram
  -> Either CompileError ( ((FcProgram), UniqueSupply)
                         , TcEnv)
hsElaborate rn_gbl_env us pgm = runExcept
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT tc_init_ctx
                              $ flip runUniqueSupplyT us
                              $ markTcError
                              $ do buildInitTcEnv pgm rn_gbl_env
                                   elabProgram pgm
  where
    tc_init_theory  = Theory mempty mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty mempty tc_init_theory
