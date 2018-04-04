{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- George says: God I hate this flag

module Frontend.HsTypeChecker where

import           Frontend.HsConstraintGen
import           Frontend.HsEntail
import           Frontend.HsRenamer
import           Frontend.HsTcMonad
import           Frontend.HsTypes

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.AssocList
import           Utils.Ctx
import           Utils.Errors
import           Utils.FreeVars
import           Utils.Kind
import           Utils.PrettyPrint        hiding ((<>))
import           Utils.Substitution
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Arrow            (second)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.List                ((\\))
import           Data.Maybe               (catMaybes, isJust)

-- * Create the typechecking environment from the renaming one
-- ------------------------------------------------------------------------------

-- | Build the initial typechecker environment from the renaming environment
buildInitTcEnv :: RnProgram -> RnEnv -> TcM ()
buildInitTcEnv pgm (RnEnv _rn_cls_infos dc_infos tc_infos) = do -- GEORGE: Assume that the initial environment is completely empty (mempty mempty mempty)
  -- Prepopulate the environment with the (user-defined) data constructor information
  mapAssocListM_ (uncurry addDataConInfoTcM) $
    mapFstWithDataAssocList (\_ info -> hs_dc_data_con info) dc_infos
  -- Prepopulate the environment with the (user-defined) type constructor information
  mapAssocListM_ (uncurry addTyConInfoTcM)   $
    mapFstWithDataAssocList (\_ info -> hs_tc_ty_con   info) tc_infos
  -- Create and store in the environment all infos for type classes
  -- (and the constructors they give rise to) -- GEORGE: UPDATE THIS WHEN YOU ADD SUPERCLASSES
  buildStoreClsInfos pgm
  where
    buildStoreClsInfos :: RnProgram -> TcM ()
    buildStoreClsInfos (PgmExp {})   = return ()
    buildStoreClsInfos (PgmInst _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmData _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmVal  _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmCls  c p) = case c of
      ClsD rn_abs rn_cs rn_cls rn_as rn_fundeps rn_method method_ty -> do
        -- Generate And Store The TyCon Info
        fc_tc <- FcTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls))) <$> getUniqueM

        -- Generate And Store The DataCon Info
        fc_dc  <- FcDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls))) <$> getUniqueM

        fd_fams <- forM (zip [0..] rn_fundeps) $ \(i,_fd) ->
          HsTF . mkName (mkSym ("F" ++ show (symOf rn_cls) ++ show (i :: Word))) <$> getUniqueM

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

        -- Continue with the rest
        buildStoreClsInfos p

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: MonadError CompileError m => Theory -> RnClsCt -> m ()
overlapCheck theory cls_ct@(ClsCt cls1 tys1) =
  case catMaybes (fmap overlaps (theory_schemes theory)) of
    msg:_ -> tcFail msg
    []    -> return ()
  where
    overlaps (_ :| scheme@(CtrScheme _ _ (ClsCt cls2 tys2)))
      | cls1 == cls2
      , Right {} <- unify [] (zipWithExact (:~:) tys1 tys2) =
        Just (text "overlapCheck:" $$ ppr cls_ct $$ ppr scheme)
      | otherwise = Nothing

-- * Constraint Entailment
-- ------------------------------------------------------------------------------

entailCs :: [RnTyVar] -> Theory -> AnnTypeCs -> TcM (AnnTypeCs, HsTySubst, EvSubst)
entailCs untchs theory cs =
  go (entailCt untchs theory) cs >>= \case
    Nothing -> return (cs, mempty, mempty)
    Just ((new_cs, ty_subst, ev_subst), cs') -> do
      (cs'', ty_subst', ev_subst') <-
        entailCs untchs theory (substInAnnTypeCs ty_subst (new_cs <> cs'))
      return (cs'', ty_subst' <> ty_subst, ev_subst' <> ev_subst)
  where
   go :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe (b, [a]))
   go _f []     = return Nothing
   go  f (x:xs) = f x >>= \case
     Just y  -> return $ Just (y,xs)
     Nothing -> (fmap . fmap) (second (x:)) (go f xs)

entailCt :: [RnTyVar] -> Theory -> AnnTypeCt -> TcM (Maybe (AnnTypeCs, HsTySubst, EvSubst))
entailCt untchs theory (AnnEqCt ct) =
  entailEq untchs (theory_axioms theory) ct >>= \case
    Nothing -> return Nothing
    Just (eq_cs, ty_subst, co_subst) ->
      return $ Just (AnnEqCt <$> eq_cs, ty_subst, coToEvSubst co_subst)
entailCt untchs theory (AnnClsCt ct) =
  entailReduce (theory_axioms theory) ct >>= \case
    Just (cls_ct, tm_subst) ->
      return $ Just ([AnnClsCt cls_ct], mempty, tmToEvSubst tm_subst)
    Nothing -> entailCls untchs (theory_schemes theory) ct >>= \case
      Nothing -> return Nothing
      Just (cls_cs, tm_subst) ->
        return $ Just (AnnClsCt <$> cls_cs, mempty, tmToEvSubst tm_subst)

-- | Entail a single type class constraint. Returns Nothing if nothing has been
--   done. May produce additional class constraints.
entailCls :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (Maybe (AnnClsCs, FcTmSubst))
entailCls _untch [] _cls_ct = return Nothing
entailCls as ((d' :| CtrScheme bs cls_cs (ClsCt cls2 tys2)):schemes) ct@(d :| ClsCt cls1 tys1)
  | cls1 == cls2
  , Right ty_subst <- unify as (zipWithExact (:~:) tys1 tys2) = do
    (d''s, ann_cls_cs) <- annotateClsCs $ substInClsCs ty_subst cls_cs
    let fc_subbed_bs = map elabMonoTy . substInTyVars ty_subst $ labelOf bs
    let ev_subst =
          d |->
           foldl
             FcTmApp
             (foldl FcTmTyApp (FcTmVar d') fc_subbed_bs)
             (FcTmVar <$> d''s)
    return $ Just (ann_cls_cs, ev_subst)
  | otherwise = entailCls as schemes ct

entailReduce :: Axioms -> AnnClsCt -> TcM (Maybe (AnnClsCt, FcTmSubst))
entailReduce axioms (d :| ClsCt cls tys) =
  case reduceAll axioms tys of
    Nothing -> return Nothing
    Just (tys', cos') -> do
      d' <- freshDictVar
      tc <- lookupClsTyCon cls
      let co = foldl FcCoApp (FcCoRefl (FcTyCon tc)) (FcCoSym <$> cos')
      return $ Just (d' :| ClsCt cls tys', d |-> FcTmCast (FcTmVar d') co)

-- | Equality contstraint entailment
entailEq :: [RnTyVar] -> Axioms -> AnnEqCt
         -> TcM (Maybe (AnnEqCs, HsTySubst, FcCoSubst))
entailEq untchs p ct = step ct
  where
    step (c :| (TyVar a :~: TyVar b))
      | a == b =
        return $ Just (mempty, mempty, c |-> FcCoRefl (elabMonoTy (TyVar a)))
    step (c :| (TyCon tc1 :~: TyCon tc2))
      | tc1 == tc2 =
        return $ Just (mempty, mempty, c |-> FcCoRefl (elabMonoTy (TyCon tc1)))
      | otherwise = unify_fail
    step (c :| (TyVar a :~: ty))
      | a `notElem` untchs, a `doesNotOccurIn` ty = unify_var c a ty
    step (c :| (ty :~: TyVar a))
      | a `notElem` untchs, a `doesNotOccurIn` ty = unify_var c a ty
    step (_ :| (TyVar _ :~: _)) = return Nothing
    step (_ :| (_ :~: TyVar _)) = return Nothing
    step (c :| (ty_fam@TyFam {} :~: ty))
      | Just (ty', co) <- reduce p ty_fam = unify_fam ty' ty c co
    step (c :| (ty :~: ty_fam@TyFam {}))
      | Just (ty', co) <- reduce p ty_fam = unify_fam ty' ty c co
    step (_ :| (TyFam _ _ :~: _)) = return Nothing
    step (_ :| (_ :~: TyFam _ _)) = return Nothing
    step (c :| (TyApp ty1 ty2 :~: TyApp ty1' ty2')) = do
      [c1, c2] <- replicateM 2 freshFcCoVar
      return $
        Just
          ( [c1 :| (ty1 :~: ty1'), c2 :| (ty2 :~: ty2')]
          , mempty
          , c |-> FcCoApp (FcCoVar c1) (FcCoVar c2))
    step (_ :| (TyCon {} :~: TyApp {})) = unify_fail
    step (_ :| (TyApp {} :~: TyCon {})) = unify_fail

    unify_var c a ty =
      return $ Just (mempty, (a |-> ty), (c |-> FcCoRefl (elabMonoTy ty)))

    unify_fam ty' ty c co = do
      c' <- freshFcCoVar
      return $
        Just ([c' :| (ty' :~: ty)], mempty, (c |-> FcCoTrans co (FcCoVar c')))

    unify_fail = tcFail $ vcat
        [ text "Equality contraint entailment failed."
        , text "Constraints"  <+> colon <+> ppr ct
        , text "Untouchables" <+> colon <+> ppr untchs
        ]

-- | Type reduction
reduce :: Axioms -> RnMonoTy -> Maybe (RnMonoTy, FcCoercion)
reduce axioms = go
  where
    go arg =
      case step arg of
        Nothing -> Nothing
        Just (new_arg, co) ->
          case go new_arg of
            Nothing               -> Just (new_arg, co)
            Just (newer_arg, co') -> Just (newer_arg, FcCoTrans co co')

    step = \case
      TyApp ty1 ty2 -> do
        ([ty1',ty2'],[co1,co2]) <- reduceAll axioms [ty1, ty2]
        return (TyApp ty1' ty2', FcCoApp co1 co2)
      TyCon _tc -> Nothing
      TyVar _x  -> Nothing
      TyFam f tys ->
        case reduceAll axioms tys of
          Just (tys', cos') -> Just (TyFam f tys', FcCoFam (rnTyFamToFcFam f) cos')
          Nothing -> findJust (matchAxiom f tys <$> axioms)

    matchAxiom :: RnTyFam -> [RnMonoTy] -> Axiom -> Maybe (RnMonoTy, FcCoercion)
    matchAxiom f1 tys (Axiom g as f2 us ty)
      | f1 == f2
      , Right subst <- unify as (zipWithExact (:~:) us tys) =
        Just
          ( applySubst subst ty
          , FcCoAx g (elabMonoTy . substInMonoTy subst . TyVar <$> as))
      | otherwise = Nothing

reduceAll :: Axioms -> [RnMonoTy] -> Maybe ([RnMonoTy],[FcCoercion])
reduceAll axioms tys =
  if any isJust m_reds
    then Just $ unzip (uncurry reduceOrReflect <$> zip tys m_reds)
    else Nothing
  where
    m_reds = reduce axioms <$> tys
    reduceOrReflect _ty (Just (new_ty, co)) = (new_ty,co)
    reduceOrReflect ty Nothing = (ty, FcCoRefl (elabMonoTy ty))

entailSuperClass :: [RnTyVar] -> Theory -> RnClsCt -> TcM ([FcType], [FcTerm], [FcCoercion])
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
  let general_cs = (AnnEqCt <$> eq_cs) <> (AnnClsCt <$> cls_cs)
  (residual_cs, ty_subst, ev_subst) <- entailCs untchs theory general_cs
  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve super class constraints" <+> colon <+> ppr residual_cs
       $$ text "From" <+> colon <+>
       ppr theory $$ text "Constraints" <+> colon <+> ppr general_cs)
  return
    ( elabMonoTy . substInMonoTy (ty_subst <> subst) . TyVar <$> bs
    , substEvInTm ev_subst . FcTmVar <$> ds
    , substEvInCo ev_subst . FcCoVar <$> cs)

-- TODO abstract over duplicated code
dictDestruction :: AnnClsCs -> TcM (MatchCtx, AnnClsCs, TcCtx)
dictDestruction [] = (,,) MCtxHole mempty <$> ask
dictDestruction ((d :| ClsCt cls tys):cs) = do
  ClassInfo ab_s sc _cls as fds fams _m mty _tc dc <-
    lookupTcEnvM tc_env_cls_info cls

  let bs = ab_s \\ as
  (bs', bs_subst) <- freshenRnTyVars bs
  let subst = bs_subst <> (buildSubst $ zipExact as tys)

  cvs <- genFreshCoVars $ length fds
  let fc_props = substFcTyInProp (elabHsTySubst subst) <$>
        map
          (\(fam, Fundep ais ai0) ->
              FcProp
                 (FcTyFam (rnTyFamToFcFam fam) (rnTyVarsToFcTypes ais))
                 (rnTyVarToFcType ai0))
          (zipExact fams fds)

  ds <- genFreshDictVars $ length sc
  fc_tys <- elabClsCs $ substInClsCs subst sc

  f <- freshRnTmVar
  let subbed_mty = substInPolyTy subst mty
  fc_mty <- elabPolyTy subbed_mty

  let new_cs = ds |: substInClsCs subst sc
  env <- extendCtxM f subbed_mty $ extendCtxM (bs) (kindOf <$> bs) ask
  (mctx, new_cs', env') <- setCtxM env $ dictDestruction $ new_cs ++ cs

  let pat =
        FcConPat
          dc
          (rnTyVarToFcTyVar <$> bs')
          (cvs |: fc_props)
          (ds  |: fc_tys ++ [rnTmVarToFcTmVar f :| fc_mty])
  return (MCtxCase d pat mctx, new_cs <> new_cs', env')

-- TODO cleanup
generateAxioms :: CtrScheme -> TcM Axioms
generateAxioms scheme@(CtrScheme _as cs (ClsCt cls tys)) = do
  fds <- lookupClsFundeps cls
  fams <- lookupClsFDFams cls
  as' <- lookupClsParams cls
  let cls_var_subst = buildSubst $ zipExact as' tys
  forM (zipExact fds fams) $ \(Fundep ais ai0, f) -> do
    let ui0:uis = substInMonoTy cls_var_subst . TyVar <$> ai0 : ais
    let free_uis = ftyvsOf uis
    subst <- determinacy free_uis cs
    let subbed_ui0 = substInMonoTy subst ui0
    if (null (ftyvsOf subbed_ui0 \\ free_uis))
      then gen_ax_fail
      else do
        g <- freshFcAxVar
        return $ Axiom g free_uis f uis subbed_ui0
  where
    gen_ax_fail =
      tcFail $
      text "Liberal Coverage Condition violation by the constraint scheme" <+>
      colon <+> ppr scheme


-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl :: RnClsDecl
            -> TcM ([FcFamDecl], FcDataDecl, [FcValBind], ProgramTheory, TcCtx)
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

  return (fc_fam_decls, fc_data_decl, fc_val_bind:[], [], ty_ctx)

-- | Check if an instance/class context is ambiguous
unambiguousCheck :: [RnTyVar] -> [RnTyVar] -> RnClsCs -> TcM ()
unambiguousCheck bs as cs = do
  subst <- determinacy as cs
  unless (bs \\ substDom subst == mempty) $
    tcFail $ text "unambiguousCheck" <+> colon <+> vcat (punctuate comma
       [ text "bs" <+> colon <+> ppr bs
       , text "as" <+> colon <+> ppr as
       , text "class constraints" <+> colon <+> ppr cs
       ])

-- | Elaborate a list of annotated dictionary variables to a list of System F term binders.
elabAnnClsCs :: AnnClsCs -> TcM [(FcTmVar, FcType)]
elabAnnClsCs = mapM (\(d :| ct) -> (,) d <$> elabClsCt ct)

-- * Data Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a datatype declaration
elabDataDecl :: RnDataDecl -> TcM (FcDataDecl, [FcFamDecl], [FcAxiomDecl])
elabDataDecl (DataD tc as dcs) = do
  -- Elaborate the type constructor
  fc_tc <- hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc
  -- Elaborate the universal type variables
  let fc_as = map (rnTyVarToFcTyVar . labelOf) as

  (fc_fams, fc_axioms) <- elabProjections tc as

  fc_dcs <- forM dcs $ \(dc, tys) -> do
    -- Elaborate the data constructor
    fc_dc <- hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc
    -- Elaborate the argument types
    (kinds, fc_tys) <- unzip <$> extendCtxKindAnnotatedTysM as (mapM wfElabMonoTy tys)
    unless (all (==KStar) kinds) $
      tcFail (text "elabDataDecl" <+> colon <+> text "not all datacon args have kind star")
    return (fc_dc, mempty, mempty, fc_tys)
  return (FcDataDecl fc_tc fc_as fc_dcs, fc_fams, fc_axioms)

-- | Elaborate the projection type functions of the type constructor
elabProjections :: RnTyCon -> [RnTyVarWithKind] -> TcM ([FcFamDecl], [FcAxiomDecl])
elabProjections tc as = do -- TODO rename as for every axiom
  tc_info       <- lookupTcEnvM tc_env_tc_info tc
  let proj_fams =  hs_tc_projs     tc_info
  let fc_tc     =  hs_tc_fc_ty_con tc_info
  fmap unzip $ forM (zip proj_fams as) $ \(proj_fam, a) -> do
    addTyFamInfoTcM proj_fam (HsTFInfo proj_fam (labelOf as) (dropLabel a))
    g <- freshFcAxVar
    a' <- freshFcTyVar KStar
    let fc_as = rnTyVarToFcTyVar <$> (labelOf as)
    let fc_a = rnTyVarToFcTyVar (labelOf a)
    let fc_fam = rnTyFamToFcFam proj_fam
    return
      ( FcFamDecl
         fc_fam
         [a']
         (dropLabel a)
      , FcAxiomDecl
         g
         fc_as
         fc_fam
         [fcTyConApp fc_tc (FcTyVar <$> fc_as)]
         (FcTyVar fc_a)
      )

-- | Extend the typing environment with some kind annotated type variables
extendCtxKindAnnotatedTysM :: [RnTyVarWithKind] -> TcM a -> TcM a
extendCtxKindAnnotatedTysM ann_as = extendCtxM as (map kindOf as)
  where
    as = map labelOf ann_as

-- * Class Instance Elaboration
-- ------------------------------------------------------------------------------

elabInsDecl :: Theory -> RnInsDecl -> TcM ([FcAxiomDecl], FcValBind, Theory)
elabInsDecl theory (InsD as ins_cs cls typats method method_tm) = do
  let tys = hsTyPatToMonoTy <$> typats
  let head_ct = ClsCt cls tys
  let bs = labelOf as \\ ftyvsOf tys
  let fc_as = rnTyVarToFcTyVar . labelOf <$> as

  overlapCheck theory head_ct
  unambiguousCheck bs (labelOf as) ins_cs

  ins_d <- freshDictVar
  ins_scheme <- freshenLclBndrs $ CtrScheme as ins_cs head_ct

  ann_ins_cs <- snd <$> annotateClsCs ins_cs

  (mctx, match_cs, match_ctx) <- dictDestruction ann_ins_cs

  axioms <- generateAxioms ins_scheme
  let i_theory = theory `tExtendAxioms`  axioms
                        `tExtendSchemes` (clsCsToSchemes ann_ins_cs)
                        `tExtendSchemes` (clsCsToSchemes match_cs)

  (fc_exis_tys, fc_tms, fc_cos) <- entailSuperClass (labelOf as) i_theory head_ct

  let ext_theory = theory `tExtendAxioms`  axioms
                          `tExtendSchemes` [ins_d :| ins_scheme]

  fc_method_tm <- do
    let theory' = i_theory `tExtendSchemes` [ins_d :| ins_scheme]
    expected_method_ty <- instMethodTy tys <$> lookupCtxM method
    setCtxM match_ctx $ extendCtxM (labelOf as) (dropLabel as) $
      elabTermWithSig (labelOf as) theory' method_tm expected_method_ty

  dtrans_ty <- extendCtxM (labelOf as) (dropLabel as) $ do
    fc_head_ty <-  wfElabClsCt head_ct
    fc_ins_cs <- wfElabClsCs ins_cs
    return $ fcTyAbs fc_as $ fcTyArr fc_ins_cs fc_head_ty

  fc_dict_transformer <- do
    binds <- elabAnnClsCs ann_ins_cs
    dc    <- lookupClsDataCon cls
    return $
      fcTmTyAbs fc_as $
       fcTmAbs binds $
         matchCtxApply mctx $
          FcTmDataCon dc `fcTmTyApp` (elabMonoTy <$> tys)
                         `fcTmTyApp` fc_exis_tys
                         `fcTmCoApp` fc_cos
                         `fcTmApp`   fc_tms
                         `FcTmApp`   fc_method_tm

  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer
  return (elabAxiom <$> axioms, fc_val_bind, ext_theory)

-- TODO better location
elabAxiom :: Axiom -> FcAxiomDecl
elabAxiom (Axiom g as f us ty) =
  FcAxiomDecl
    g
    (rnTyVarToFcTyVar <$> as)
    (rnTyFamToFcFam f)
    (elabMonoTy <$> us)
    (elabMonoTy ty)

clsCsToSchemes :: AnnClsCs -> AnnSchemes
clsCsToSchemes = (fmap . fmap) (CtrScheme [] [])

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

  let theory' = theory `tExtendSchemes` clsCsToSchemes (match_ccs <> given_ccs)
  let untouchables = untchs <> labelOf as
  let wanted_cs =
        (AnnEqCt <$> (c :| (ty1 :~: ty2)) : wanted_eqs) <> (AnnClsCt <$> wanted_ccs)
  (residual_cs, ty_subst, ev_subst) <- entailCs untouchables theory' wanted_cs

  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve constraints" <+>
       colon <+>
       ppr residual_cs $$ text "From" <+>
       colon <+> ppr theory $$ text "Wanted" <+> colon <+> ppr wanted_cs)

  dbinds <- elabAnnClsCs given_ccs
  let fc_ty_subst = elabHsTySubst ty_subst
  return $
    fcTmTyAbs (rnTyVarToFcTyVar <$> (labelOf as)) $
    fcTmAbs dbinds $
    matchCtxApply mctx $
    substFcTyInTm fc_ty_subst $
    substEvInTm ev_subst $ FcTmCast fc_tm (FcCoVar c)

-- * Type Inference With Constraint Simplification
-- ------------------------------------------------------------------------------

-- TODO probably wrong
elabTermSimpl :: Theory -> RnTerm -> TcM (RnPolyTy, FcTerm)
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  let wanted_cs = (AnnEqCt <$> wanted_eqs) <> (AnnClsCt <$> wanted_ccs)
  (residual_cs, ty_subst, ev_subst) <- entailCs [] theory wanted_cs

  -- Generalize the type
  let new_mono_ty = substInMonoTy ty_subst mono_ty
  let new_cs      = map dropLabel $ filterAnnClsCs residual_cs
  let new_as      = ftyvsOf new_mono_ty
  let gen_ty      = constructPolyTy (map (\a -> a :| kindOf a) new_as, new_cs, new_mono_ty)

  -- Elaborate the term
  let fc_as = map rnTyVarToFcTyVar new_as
  let refined_fc_tm = substFcTyInTm (elabHsTySubst ty_subst) fc_tm
  dbinds   <- elabAnnClsCs $ filterAnnClsCs residual_cs
  let full_fc_tm = fcTmTyAbs fc_as $
                     fcTmAbs dbinds $
                       substEvInTm ev_subst refined_fc_tm

  return (gen_ty, full_fc_tm)
  where
    -- TODO meh
    filterAnnClsCs (AnnClsCt ct:cs) = ct:filterAnnClsCs cs
    filterAnnClsCs (_ct:cs)         =    filterAnnClsCs cs
    filterAnnClsCs []               = []

-- * Value Binding Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a top-level value binding
elabValBind :: Theory -> RnValBind -> TcM (FcValBind, TcCtx)
elabValBind theory (ValBind a m_ty tm) = do
  (ty,fc_tm) <- case m_ty of
    Nothing -> elabTermSimpl theory tm
    Just ty -> do
      fc_tm <- elabTermWithSig [] theory tm ty
      return (ty,fc_tm)
  ctx <- ask
  fc_ty <- elabPolyTy ty
  let fc_val_bind = FcValBind (rnTmVarToFcTmVar a) fc_ty fc_tm
  return (fc_val_bind, extendCtx ctx a ty)

-- * Program Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a program
elabProgram :: Theory -> RnProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnPolyTy        {- Term type (MonoTy?)      -}
                   , Theory )    {- Final program theory     -}
-- Elaborate the program expression
elabProgram theory (PgmExp tm) = do
  (ty, fc_tm) <- elabTermSimpl theory tm
  return (FcPgmTerm fc_tm, ty, theory) -- GEORGE: You should actually return the ones we have accumulated.

-- Elaborate a class declaration
elabProgram theory (PgmCls cls_decl pgm) = do
  (fc_fam_decls, fc_data_decl, fc_val_binds, ext_theory, ext_ty_env) <-
    elabClsDecl cls_decl
  (fc_pgm, ty, final_theory) <-
    setCtxM ext_ty_env (elabProgram (theory `tExtendSchemes` ext_theory) pgm)
  let fc_pgm_data_val_decls =
        FcPgmDataDecl
          fc_data_decl
             (foldl (flip FcPgmValDecl) fc_pgm fc_val_binds)
  let fc_program = foldr FcPgmFamDecl fc_pgm_data_val_decls fc_fam_decls
  return (fc_program, ty, final_theory)

-- | Elaborate a class instance
elabProgram theory (PgmInst ins_decl pgm) = do
  (fc_axiom_decls, fc_val_bind, ext_theory) <- elabInsDecl theory ins_decl
  (fc_pgm, ty, final_theory) <- elabProgram ext_theory pgm
  let fc_program =
        foldr (FcPgmAxiomDecl) (FcPgmValDecl fc_val_bind fc_pgm) fc_axiom_decls
  return (fc_program, ty, final_theory)

-- Elaborate a datatype declaration
elabProgram theory (PgmData data_decl pgm) = do
  (fc_data_decl, fc_fam_decls, fc_ax_decls)  <- elabDataDecl data_decl
  (fc_pgm, ty, final_theory) <- elabProgram theory pgm
  let fc_program =
        FcPgmDataDecl
          fc_data_decl
          (foldr
            FcPgmFamDecl
              (foldr FcPgmAxiomDecl fc_pgm fc_ax_decls)
              fc_fam_decls
          )
  return (fc_program, ty, final_theory)

-- Elaborate a top-level value binding
elabProgram theory (PgmVal val_bind pgm) = do
  (fc_val_bind, ext_ctx) <- elabValBind theory val_bind
  (fc_pgm, ty, final_theory) <- setCtxM ext_ctx $ elabProgram theory pgm
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_program, ty, final_theory)

-- * Invoke the complete type checker
-- ------------------------------------------------------------------------------

hsElaborate ::
     RnEnv
  -> UniqueSupply
  -> RnProgram
  -> Either CompileError ( (((FcProgram, RnPolyTy, Theory)), UniqueSupply)
                         , TcEnv)
hsElaborate rn_gbl_env us pgm = runExcept
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT tc_init_ctx
                              $ flip runUniqueSupplyT us
                              $ markTcError
                              $ do buildInitTcEnv pgm rn_gbl_env
                                   elabProgram tc_init_theory pgm
  where
    tc_init_theory  = Theory mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty mempty
