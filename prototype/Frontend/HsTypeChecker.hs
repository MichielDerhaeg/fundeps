{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- George says: God I hate this flag

module Frontend.HsTypeChecker (hsElaborate) where

import Frontend.HsTypes
import Frontend.HsRenamer

import Backend.FcTypes

import Utils.Substitution
import Utils.FreeVars
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Annotated
import Utils.Ctx
import Utils.PrettyPrint hiding ((<>))
import Utils.Utils
import Utils.Errors

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Arrow (second)
import Data.Either (partitionEithers)
import Data.List (nub, (\\), intersect)
import Data.Maybe (catMaybes, isJust)

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
      ClsD _rn_abs rn_cs rn_cls rn_as rn_fundeps rn_method method_ty -> do
        -- Generate And Store The TyCon Info
        fc_tc <- FcTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls))) <$> getUniqueM

        -- Generate And Store The DataCon Info
        fc_dc  <- FcDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls))) <$> getUniqueM

        fd_fams <- forM (zip [0..] rn_fundeps) $ \(i,_fd) ->
          HsTF . mkName (mkSym ("F" ++ show (symOf rn_cls) ++ show i)) <$> getUniqueM

        -- Generate And Store The Class Info
        let cls_info =
              ClassInfo
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

-- | Add a renamed class name to the state
addClsInfoTcM :: RnClass -> ClassInfo -> TcM ()
addClsInfoTcM cls info = modify $ \s ->
  s { tc_env_cls_info = extendAssocList cls info (tc_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoTcM :: RnDataCon -> HsDataConInfo -> TcM ()
addDataConInfoTcM dc info = modify $ \s ->
  s { tc_env_dc_info = extendAssocList dc info (tc_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoTcM :: RnTyCon -> HsTyConInfo -> TcM ()
addTyConInfoTcM tc info = modify $ \s ->
  s { tc_env_tc_info = extendAssocList tc info (tc_env_tc_info s) }

-- | Add a renamed tyfam name to the state
addTyFamInfoTcM :: RnTyFam -> HsTyFamInfo -> TcM ()
addTyFamInfoTcM tf info = modify $ \s ->
  s { tc_env_tf_info = extendAssocList tf info (tc_env_tf_info s)}

-- * Type Checking Monad
-- ------------------------------------------------------------------------------

type TcM = UniqueSupplyT (ReaderT TcCtx (StateT TcEnv (Except CompileError)))

data TcEnv = TcEnv
  { tc_env_cls_info :: AssocList RnClass   ClassInfo
  , tc_env_dc_info  :: AssocList RnDataCon HsDataConInfo
  , tc_env_tc_info  :: AssocList RnTyCon   HsTyConInfo
  , tc_env_tf_info  :: AssocList RnTyFam   HsTyFamInfo
  }

instance PrettyPrint TcEnv where
  ppr (TcEnv cls_infos dc_infos tc_infos tf_infos)
    = braces $ vcat $ punctuate comma
    [ text "tc_env_cls_info" <+> colon <+> ppr cls_infos
    , text "tc_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "tc_env_tc_info"  <+> colon <+> ppr tc_infos
    , text "tc_env_tf_info"  <+> colon <+> ppr tf_infos
    ]
  needsParens _ = False

-- * Lookup data and type constructors for a class
-- ------------------------------------------------------------------------------

-- GEORGE: 1. Rename TcEnv to TcGblEnv
--         2. It's exactly the same as lookupFcGblEnv. Abstract over both.

-- | Lookup something in the global environment
lookupTcEnvM ::
     (Eq a, PrettyPrint a, MonadError CompileError m, MonadState s m)
  => (s -> AssocList a b)
  -> a
  -> m b
lookupTcEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> tcFail (text "lookupTcEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup a type constructor
lookupTyCon :: RnTyCon -> TcM FcTyCon
lookupTyCon tc = hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc

-- | Lookup the kind of a type constructor
tyConKind :: RnTyCon -> TcM Kind
tyConKind tc = do
  info <- lookupTcEnvM tc_env_tc_info tc
  return (mkArrowKind (map kindOf (hs_tc_type_args info)) KStar)

-- | Lookup a data constructor
lookupDataCon :: RnDataCon -> TcM FcDataCon
lookupDataCon dc = hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc

-- | Lookup the kinds of the arguments
clsArgKinds :: RnClass -> TcM [Kind]
clsArgKinds cls = map kindOf . cls_type_args <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc type constructor for a class
lookupClsTyCon :: RnClass -> TcM FcTyCon
lookupClsTyCon cls = cls_tycon <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc data constructor for a class
lookupClsDataCon :: RnClass -> TcM FcDataCon
lookupClsDataCon cls = cls_datacon <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the signature of a data constructor in pieces
dataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
dataConSig dc = lookupTcEnvM tc_env_dc_info dc >>= \info ->
  return ( hs_dc_univ    info
         , hs_dc_arg_tys info
         , hs_dc_parent  info )

-- | Get the superclasses of a class
lookupClsSuper :: RnClass -> TcM RnClsCs
lookupClsSuper cls = cls_super <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the parameter of the class
lookupClsParam :: RnClass -> TcM RnTyVar
lookupClsParam cls = do
  info <- lookupTcEnvM tc_env_cls_info cls
  case cls_type_args info of
    [a] -> return a
    _   -> tcFail (text "lookupClsParam")

-- | Get the type parameters of the class
--   TODO replace old one
lookupClsParams :: RnClass -> TcM [RnTyVar]
lookupClsParams cls = cls_type_args <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the functional dependencies of the class
lookupClsFundeps :: RnClass -> TcM [RnFundep]
lookupClsFundeps cls = cls_fundeps <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the projection type families of the type constructor
lookupTyConProj :: RnTyCon -> TcM [RnTyFam]
lookupTyConProj tc = hs_tc_projs <$> lookupTcEnvM tc_env_tc_info tc

-- | Get the type families of the functional dependencies of the type class
lookupClsFDFams :: RnClass -> TcM [RnTyFam]
lookupClsFDFams cls = cls_fd_fams <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the type family information
lookupTyFamInfo :: RnTyFam -> TcM HsTyFamInfo
lookupTyFamInfo f = lookupTcEnvM tc_env_tf_info f

-- | Get the type arguments of the type constructor
lookupTyConArgs :: RnTyCon -> TcM [RnTyVar]
lookupTyConArgs tc = hs_tc_type_args <$> lookupTcEnvM tc_env_tc_info tc

-- | Get the parent type constructor of the data constructor
lookupDataConTyCon :: RnDataCon -> TcM RnTyCon
lookupDataConTyCon dc = hs_dc_parent <$> lookupTcEnvM tc_env_dc_info dc

-- * Type and Constraint Elaboration (With Well-formedness (well-scopedness) Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
wfElabMonoTy :: RnMonoTy -> TcM (Kind, FcType)
wfElabMonoTy (TyCon tc) = do
  kind  <- tyConKind tc
  fc_tc <- lookupTyCon tc
  return (kind, FcTyCon fc_tc)
wfElabMonoTy (TyApp ty1 ty2) = do
  (k1, fc_ty1) <- wfElabMonoTy ty1
  (k2, fc_ty2) <- wfElabMonoTy ty2
  case k1 of
    KArr k1a k1b
      | k1a == k2 -> return (k1b, FcTyApp fc_ty1 fc_ty2)
    _other_kind   -> tcFail (text "wfElabMonoTy" <+> colon <+> text "TyApp")
wfElabMonoTy (TyVar v) = do
  kind <- lookupCtxM v
  return (kind, rnTyVarToFcType v)
wfElabMonoTy (TyFam f tys) = do
  HsTFInfo _f as k <- lookupTyFamInfo f
  (ks, fc_tys) <- unzip <$> mapM wfElabMonoTy tys
  unless ((kindOf <$> as) == ks) $
    tcFail (text "wfElabMonoTy: kind mismatch (TyFam)")
  return (k, FcTyFam (rnTyFamToFcFam f) fc_tys)

-- | Elaborate a qualified type
wfElabQualTy :: RnQualTy -> TcM (Kind, FcType)
wfElabQualTy (QMono ty)    = wfElabMonoTy ty
wfElabQualTy (QQual ct ty) = do
  fc_ty1         <- wfElabClsCt ct
  (kind, fc_ty2) <- wfElabQualTy ty
  unless (kind == KStar) $
    tcFail (text "wfElabQualTy" <+> colon <+> text "QQual")
  return (KStar, mkFcArrowTy fc_ty1 fc_ty2)

-- | Elaborate a class constraint
wfElabClsCt :: RnClsCt -> TcM FcType
wfElabClsCt (ClsCt cls tys) = do
  (kinds, fc_tys) <- unzip <$> mapM wfElabMonoTy tys
  clsArgKinds cls >>= \case
    ks | ks == kinds -> do
      fc_tc <- lookupClsTyCon cls
      return (fcTyApp (FcTyCon fc_tc) fc_tys)
    _other_kind -> tcFail (text "wfElabClsCt")

-- | Elaborate a list of class constraints
wfElabClsCs :: RnClsCs -> TcM [FcType]
wfElabClsCs = mapM wfElabClsCt

-- | Elaborate an equality constraint
wfElabEqCt :: EqCt -> TcM FcProp
wfElabEqCt (ty1 :~: ty2) = do
  (k1, fc_ty1) <- wfElabMonoTy ty1
  (k2, fc_ty2) <- wfElabMonoTy ty2
  unless (k1 == k2) $
    throwErrorM $ text "wfElabEqCt" <+> colon <+> text "kind mismatch"
  return $ FcProp fc_ty1 fc_ty2

-- | Elaborate a polytype
wfElabPolyTy :: RnPolyTy -> TcM (Kind, FcType)
wfElabPolyTy (PQual ty) = wfElabQualTy ty
wfElabPolyTy (PPoly (a :| _) ty) = do
  notInCtxM a {- GEORGE: ensure is unbound -}
  (kind, fc_ty) <- extendCtxM a (kindOf a) (wfElabPolyTy ty)
  unless (kind == KStar) $
    tcFail (text "wfElabPolyTy" <+> colon <+> text "PPoly")
  return (KStar, FcTyAbs (rnTyVarToFcTyVar a) fc_ty)

-- * Type and Constraint Elaboration (Without Well-scopedness Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
elabMonoTy :: RnMonoTy -> TcM FcType
elabMonoTy (TyCon tc)      = FcTyCon <$> lookupTyCon tc
elabMonoTy (TyApp ty1 ty2) = FcTyApp <$> elabMonoTy ty1 <*> elabMonoTy ty2
elabMonoTy (TyVar v)       = return (rnTyVarToFcType v)
elabMonoTy (TyFam f tys)   = FcTyFam (rnTyFamToFcFam f) <$> mapM elabMonoTy tys

-- | TODO replace old elabMonoTy
elabMonoTy' :: RnMonoTy -> FcType
elabMonoTy' (TyCon tc)      = FcTyCon $ rnTyConToFcTyCon tc
elabMonoTy' (TyApp ty1 ty2) = FcTyApp (elabMonoTy' ty1) (elabMonoTy' ty2)
elabMonoTy' (TyVar v)       = rnTyVarToFcType v
elabMonoTy' (TyFam f tys)   = FcTyFam (rnTyFamToFcFam f) (elabMonoTy' <$> tys)

-- | Elaborate a class constaint
elabClsCt :: RnClsCt -> TcM FcType
elabClsCt (ClsCt cls tys) =
  fcTyApp <$> (FcTyCon <$> lookupClsTyCon cls) <*> mapM elabMonoTy tys

-- | Elaborate an equality constraint
elabEqCt :: EqCt -> TcM FcProp
elabEqCt (ty1 :~: ty2) = FcProp <$> elabMonoTy ty1 <*> elabMonoTy ty2

-- | Elaborate a class constaint scheme
elabScheme :: CtrScheme -> TcM FcType
elabScheme (CtrScheme as cs cls_ct) = elabAbs as $ elabImpls cs $ elabClsCt cls_ct
  where
    elabImpls (ct1:cs') fc = mkFcArrowTy <$> elabClsCt ct1 <*> elabImpls cs' fc
    elabImpls [] fc = fc
    elabAbs ((a :| _):as') fc = FcTyAbs (rnTyVarToFcTyVar a) <$> elabAbs as' fc
    elabAbs [] fc = fc

-- | Elaborate a polytype
elabPolyTy :: RnPolyTy -> TcM FcType
elabPolyTy (PQual ty) = elabQualTy ty
elabPolyTy (PPoly (a :| _) ty) =
  FcTyAbs (rnTyVarToFcTyVar a) <$> elabPolyTy ty

-- | Elaborate a qualified type
elabQualTy :: RnQualTy -> TcM FcType
elabQualTy (QQual cls_ct ty) =
  mkFcArrowTy <$> elabClsCt cls_ct <*> elabQualTy ty
elabQualTy (QMono ty) = elabMonoTy ty

-- * Constraint store
-- ------------------------------------------------------------------------------

-- | ConstraintStore containing both the equality constraints and named class constraints
data ConstraintStore = CS AnnEqCs AnnClsCs

instance Monoid ConstraintStore where
  mempty = CS mempty mempty
  mappend (CS eqs1 ccs1) (CS eqs2 ccs2)
    = CS (mappend eqs1 eqs2) (mappend ccs1 ccs2)

-- | Type inference generation monad
newtype GenM a = GenM (StateT ConstraintStore TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState ConstraintStore, MonadReader TcCtx, MonadError CompileError)

-- GEORGE: All this is bad. We should not store the unique supply within the
-- global environment, rather wrap our monads with the UniqueSupplyT transformer
instance MonadUnique GenM where
  getUniqueSupplyM = liftGenM getUniqueSupplyM

-- | Get out of the constraint generation monad
runGenM :: GenM a -> TcM (a, AnnEqCs, AnnClsCs)
runGenM (GenM m) = do
    (v , (CS eqs ccs)) <- runStateT m mempty
    return (v, eqs, ccs)

-- | Lift TcM into GenM
liftGenM :: TcM a -> GenM a
liftGenM m = GenM (StateT (\cs -> m >>= \x -> return (x, cs)))

-- | Add some equality constraints in the constraint store
storeEqCs :: AnnEqCs -> GenM ()
storeEqCs cs = modify (\(CS eqs ccs) -> CS (cs ++ eqs) ccs)

-- | Add some (variable-annotated) class constraints in the constraint store
storeClsCs :: AnnClsCs -> GenM ()
storeClsCs cs = modify (\(CS eqs ccs) -> CS eqs (mappend ccs cs))

-- | Add many type variables to the typing context
extendTcCtxTysM :: MonadReader TcCtx m => [RnTyVar] -> m a -> m a
extendTcCtxTysM []     m = m
extendTcCtxTysM ty_vars m = foldl (\m' a -> extendCtxM a (kindOf a) m') m ty_vars

-- * Term Elaboration
-- ------------------------------------------------------------------------------

-- | Freshen up a list of type variables. Return
--   a) the list of fresh variables (NB: same length as input)
--   b) the substitution from the old to the fresh ones
freshenRnTyVars :: [RnTyVar] -> TcM ([RnTyVar], HsTySubst)
freshenRnTyVars tvs = do
  new_tvs <- mapM freshRnTyVar (map kindOf tvs)
  let subst = buildRnSubst (zipExact tvs new_tvs)
  return (new_tvs, subst)

-- | Instantiate a polytype with fresh unification variables
instPolyTy :: RnPolyTy -> TcM ([RnTyVar], RnClsCs, RnMonoTy)
instPolyTy poly_ty = do
  (bs,subst) <- freshenRnTyVars (map labelOf as)
  let new_cs = substInClsCs subst cs
  let new_ty = substInMonoTy subst ty
  return (bs, new_cs, new_ty)
  where
    (as, cs, ty) = destructPolyTy poly_ty

-- | Generate a number of fresh dictionary variables
genFreshDictVars :: MonadUnique m => Int -> m [DictVar]
genFreshDictVars n = replicateM n freshDictVar

-- | Annotate a list of constraints with a fresh dictionary variables
annotateClsCs :: RnClsCs -> TcM ([DictVar], AnnClsCs)
annotateClsCs cs = do
  ds <- genFreshDictVars (length cs)
  return (ds, (ds) |: (cs))

genFreshCoVars :: MonadUnique m => Int -> m [FcCoVar]
genFreshCoVars n = replicateM n freshFcCoVar

annotateEqCs :: EqCs -> TcM ([FcCoVar], AnnEqCs)
annotateEqCs eq_cs = do
  cs <- genFreshCoVars (length eq_cs)
  return (cs, cs |: eq_cs)

-- | Elaborate a term
elabTerm :: RnTerm -> GenM (RnMonoTy, FcTerm)
elabTerm (TmApp tm1 tm2)   = elabTmApp tm1 tm2
elabTerm (TmAbs x tm)      = elabTmAbs x tm
elabTerm (TmVar x)         = elabTmVar x
elabTerm (TmCon dc)        = liftGenM (elabTmCon dc)
elabTerm (TmLet x tm1 tm2) = elabTmLet x tm1 tm2
elabTerm (TmCase scr alts) = elabTmCase scr alts

-- | Elaborate a term application
elabTmApp :: RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmApp tm1 tm2 = do
  (ty1, fc_tm1) <- elabTerm tm1
  (ty2, fc_tm2) <- elabTerm tm2
  a <- TyVar <$> freshRnTyVar KStar
  c <- freshFcCoVar
  storeEqCs [c :| (mkRnArrowTy [ty2] a :~: ty1)]
  -- TODO plug in
  let fc_tm = FcTmApp (FcTmCast fc_tm1 (FcCoVar c)) fc_tm2
  return (a, FcTmApp fc_tm1 fc_tm2)

-- | Elaborate a lambda abstraction
elabTmAbs :: RnTmVar -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmAbs x tm = do
  liftGenM (notInCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty, fc_tm) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm
  let result = FcTmAbs (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm
  return (mkRnArrowTy [TyVar tv] ty, result)

-- | Elaborate a term variable
elabTmVar :: RnTmVar -> GenM (RnMonoTy, FcTerm)
elabTmVar x = do
  poly_ty     <- liftGenM (lookupCtxM x)
  (bs,cs,ty)  <- liftGenM (instPolyTy poly_ty)
  as          <- intersect bs <$> unboundElemsOf ty -- TODO check if subset of bs?
  let bs'     =  bs \\ as
  subst       <- liftGenM (determinacy as cs)
  _           <- extendTcCtxTysM bs $ liftGenM (wfElabClsCs cs)
  (ds,ann_cs) <- liftGenM (annotateClsCs (substInClsCs subst cs))

  -- store the constraints
  storeClsCs ann_cs

  -- System F representation
  let fc_ds = map FcTmVar ds
  let fc_as = rnTyVarToFcType <$> as
  fc_bs    <- liftGenM $ mapM (elabMonoTy . substInTyVar subst) bs'
  let fc_tm = fcTmApp (fcTmTyApp (rnTmVarToFcTerm x) (fc_as <> fc_bs)) fc_ds
  return (ty, fc_tm)

-- | Elaborate a let binding (monomorphic, recursive)
elabTmLet :: RnTmVar -> RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmLet x tm1 tm2 = do
  liftGenM (notInCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  c  <- freshFcCoVar
  (ty1, fc_tm1) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm1
  (ty2, fc_tm2) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm2 -- could have also passed ty1 but it is the same
  storeEqCs [c :| (TyVar tv :~: ty1)]
  let fc_tm = FcTmLet (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm1 fc_tm2
  return (ty2, fc_tm)

-- | Elaborate a data constructor
elabTmCon :: RnDataCon -> TcM (RnMonoTy, FcTerm)
elabTmCon dc = do
  (bs, arg_tys, tc) <- freshenDataConSig dc
  fc_dc <- lookupDataCon dc

  -- Haskell monotype
  let mono_ty = mkRnArrowTy arg_tys (mkTyConApp tc (map TyVar bs))
  -- System F term
  let fc_tm = fcTmTyApp (FcTmDataCon fc_dc) (rnTyVarsToFcTypes bs)

  return (mono_ty, fc_tm)

freshenDataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
freshenDataConSig dc = do
  (as, arg_tys, tc) <- dataConSig dc
  (bs, subst) <- freshenRnTyVars as
  return (bs, substInMonoTy subst <$> arg_tys, tc)

-- | Cast a list of polytypes to monotypes. Fail if not possible
polyTysToMonoTysM :: MonadError CompileError m => [PolyTy a] -> m [MonoTy a]
polyTysToMonoTysM []       = return []
polyTysToMonoTysM (ty:tys) = case polyTyToMonoTy ty of
  Just mono_ty -> fmap (mono_ty:) (polyTysToMonoTysM tys)
  Nothing      -> tcFail (text "polyTysToMonoTysM" <+> colon <+> text "non-monotype")

-- | Elaborate a case expression
elabTmCase :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase scr alts = do
  (scr_ty, fc_scr) <- elabTerm scr               -- Elaborate the scrutinee
  rhs_ty  <- TyVar <$> freshRnTyVar KStar        -- Generate a fresh type variable for the result
  fc_alts <- mapM (elabHsAlt scr_ty rhs_ty) alts -- Check the alternatives
  return (rhs_ty, FcTmCase fc_scr fc_alts)

-- | Elaborate a case alternative
elabHsAlt :: RnMonoTy {- Type of the scrutinee -}
          -> RnMonoTy {- Result type           -}
          -> RnAlt    {- Case alternative      -}
          -> GenM FcAlt
elabHsAlt scr_ty res_ty (HsAlt (HsPat dc xs) rhs) = do
  -- Get the constructor's signature
  (as, orig_arg_tys, tc) <- liftGenM (dataConSig dc)
  -- Get the constructor's System F representation
  fc_dc <- liftGenM (lookupDataCon dc)

  -- Generate fresh universal type variables for the universal tvs
  (bs, ty_subst) <- liftGenM (freshenRnTyVars as)
  -- Apply the renaming substitution to the argument types
  let arg_tys = substInMonoTy ty_subst <$> orig_arg_tys
  -- Type check the right hand side
  (rhs_ty, fc_rhs) <- extendCtxM xs (monoTyToPolyTy <$> arg_tys) (elabTerm rhs)
  -- The scrutinee type must match the pattern type
  (_cs, ann_cs) <- liftGenM $ annotateEqCs
    [ scr_ty :~: foldl TyApp (TyCon tc) (map TyVar bs)
  -- All right hand sides should be the same
    , res_ty :~: rhs_ty ]
  storeEqCs ann_cs

  let fc_tys = elabMonoTy' <$> arg_tys
  return (FcAlt (FcConPat fc_dc [] [] ((rnTmVarToFcTmVar <$> xs) |: fc_tys)) fc_rhs)

-- | Elaborate a case expression TODO replace with old elabTmCase
elabTmCase' :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase' scr alts = do
  (scr_ty, fc_scr) <- elabTerm scr
  result_ty <- TyVar <$> freshRnTyVar KStar
  c <- freshFcCoVar
  (tycon_ty, as') <- liftGenM $ inferTyConTy alts
  fc_alts <-
    forM alts $ \(HsAlt (HsPat dc xs) rhs) -> do
      mapM_ notInCtxM xs
      (as, tys, _tc) <- liftGenM $ dataConSig dc
      let arg_tys' = substInMonoTy (buildSubst (zip as (TyVar <$> as'))) <$> tys
      fc_dc <- liftGenM (lookupDataCon dc)
      let fc_tys = elabMonoTy' <$> arg_tys'
      (rhs_ty, fc_rhs) <- extendCtxM xs (monoTyToPolyTy <$> arg_tys') $ elabTerm rhs
      c' <- freshFcCoVar
      storeEqCs [c' :| (rhs_ty :~: result_ty)]
      return
        (FcAlt
           (FcConPat fc_dc [] [] ((rnTmVarToFcTmVar <$> xs) |: fc_tys))
           (FcTmCast fc_rhs (FcCoVar c')))
  storeEqCs [c :| (scr_ty :~: tycon_ty)]
  return (result_ty, FcTmCase (FcTmCast fc_scr (FcCoVar c)) fc_alts)

-- | Manually type check data constructors, not very clean but allows us to use
--   a single coercion to cast the scrutinee
inferTyConTy :: [RnAlt] -> TcM (RnMonoTy, [RnTyVar])
inferTyConTy alts = do
  (tc:tcs) <- forM alts $ \(HsAlt (HsPat dc _) _) -> lookupDataConTyCon dc
  unless (all (== tc) tcs) $ tcFail (text "TODO")
  as <- lookupTyConArgs tc
  bs <- mapM (freshRnTyVar . kindOf) as
  return (mkTyConApp tc (TyVar <$> bs), bs)

-- | Covert a renamed type variable to a System F type
rnTyVarToFcType :: RnTyVar -> FcType
rnTyVarToFcType = FcTyVar . rnTyVarToFcTyVar

-- | Covert a list of renamed type variables to a list of System F types
rnTyVarsToFcTypes :: [RnTyVar] -> [FcType]
rnTyVarsToFcTypes = map rnTyVarToFcType

-- | Covert a renamed term variable to a System F term
rnTmVarToFcTerm :: RnTmVar -> FcTerm
rnTmVarToFcTerm = FcTmVar . rnTmVarToFcTmVar

-- | TODO better place?
rnTyFamToFcFam :: RnTyFam -> FcTyFam
rnTyFamToFcFam (HsTF name) = FcFV name

rnTyConToFcTyCon :: RnTyCon -> FcTyCon
rnTyConToFcTyCon (HsTC name) = FcTC name

-- * Type Unification
-- ------------------------------------------------------------------------------

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError CompileError m => [RnTyVar] -> EqCs -> m HsTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- go one_step eqs
  = do subst2 <- unify untchs (substInEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = tcFail $ vcat [ text "Unification failed."
                              , text "Residual constraints" <+> colon <+> ppr eqs
                              , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: EqCt -> Maybe (HsTySubst, EqCs)
    one_step (TyVar v1 :~: TyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step (TyVar v :~: ty)
      | v `notElem` untchs, v `doesNotOccurIn` ty = Just (v |-> ty, [])
    one_step (ty :~: TyVar v)
      | v `notElem` untchs, v `doesNotOccurIn` ty = Just (v |-> ty, [])
    one_step (_ :~: TyVar _) = Nothing
    one_step (TyVar _ :~: _) = Nothing
    one_step (TyCon tc1 :~: TyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
      | otherwise  = Nothing
    one_step (TyApp ty1 ty2 :~: TyApp ty3 ty4)
      = Just (mempty, [ty1 :~: ty3, ty2 :~: ty4])
    one_step (TyCon {} :~: TyApp {}) = Nothing
    one_step (TyApp {} :~: TyCon {}) = Nothing
    one_step (TyFam {} :~: _) = Nothing
    one_step (_ :~: TyFam {}) = Nothing

    go :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
    go _p []     = Nothing
    go  p (x:xs) | Just y <- p x = Just (y, xs)
                 | otherwise     = second (x:) <$> go p xs

-- | Occurs check.
--   Returns `True` if the given variable does not occur in the given type.
doesNotOccurIn :: RnTyVar -> RnMonoTy -> Bool
doesNotOccurIn _ TyCon {}        = True
doesNotOccurIn a (TyApp ty1 ty2) = a `doesNotOccurIn` ty1 && a `doesNotOccurIn` ty2
doesNotOccurIn a (TyVar b)       = a /= b
doesNotOccurIn a (TyFam _ tys)   = (a `doesNotOccurIn`) `all` tys

-- | Type Unification.
unify' :: [RnTyVar] -> Axioms -> AnnEqCs -> TcM (AnnEqCs, HsTySubst, FcCoSubst)
unify' _untchs _p []    = return (mempty,mempty,mempty)
unify'  untchs  p eq_cs =
  go step eq_cs >>= \case
    Nothing -> return (eq_cs, mempty, mempty)
    Just ((new_cs, ty_subst, ev_subst), eq_cs') -> do
      (eq_cs'', ty_subst', ev_subst') <-
        unify' untchs p (substInAnnEqCs ty_subst (new_cs <> eq_cs'))
      return (eq_cs'', ty_subst <> ty_subst', ev_subst <> ev_subst')
  where
    go :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe (b, [a]))
    go _f []     = return Nothing
    go  f (x:xs) = f x >>= \case
      Just y  -> return $ Just (y,xs)
      Nothing -> (fmap . fmap) (second (x:)) (go f xs)

    step (_ :| (TyVar a :~: TyVar b))
      | a == b = return $ Just mempty
    step (_ :| (TyCon tc1 :~: TyCon tc2))
      | tc1 == tc2 = return $ Just mempty
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

    unify_var c a ty = do
      fc_ty <- elabMonoTy ty
      return $ Just (mempty, (a |-> ty), (c |-> FcCoRefl fc_ty))

    unify_fam ty' ty c co = do
      c' <- freshFcCoVar
      return $
        Just ([c' :| (ty' :~: ty)], mempty, (c |-> FcCoTrans co (FcCoVar c')))

    unify_fail = tcFail $ vcat
        [ text "Unification failed."
        , text "Constraints"  <+> colon <+> ppr eq_cs
        , text "Untouchables" <+> colon <+> ppr untchs
        ]

-- | Type reduction
reduce :: Axioms -> RnMonoTy -> Maybe (RnMonoTy, FcCoercion)
reduce axioms = repeatedReduce
  where
    go = \case
      TyApp ty1 ty2 ->
        case (repeatedReduce ty1, repeatedReduce ty2) of
          (Nothing, Nothing) -> Nothing
          (l, r) ->
            let (ty1', co1) = reduceOrReflect ty1 l in
            let (ty2', co2) = reduceOrReflect ty2 r in
               Just (TyApp ty1' ty2', FcCoApp co1 co2)
      TyCon _tc -> Nothing
      TyVar _x  -> Nothing
      TyFam f tys ->
        let m_reds = repeatedReduce <$> tys
        in if any isJust m_reds
             then let (tys', cos') =
                        unzip (uncurry reduceOrReflect <$> zip tys m_reds)
                  in Just (TyFam f tys', FcCoFam (rnTyFamToFcFam f) cos')
             else findJust (matchAxiom f tys <$> axioms)

    matchAxiom :: RnTyFam -> [RnMonoTy] -> Axiom -> Maybe (RnMonoTy, FcCoercion)
    matchAxiom f1 tys (Axiom g as f2 us ty)
      | f1 == f2
      , Right subst <- unify as (zipWithExact (:~:) us tys) =
        Just
          ( applySubst subst ty
          , FcCoAx g (elabMonoTy' . substInMonoTy subst . TyVar <$> as))
      | otherwise = Nothing

    repeatedReduce :: RnMonoTy -> Maybe (RnMonoTy, FcCoercion)
    repeatedReduce arg =
      case go arg of
        Nothing -> Nothing
        Just (new_arg, co) ->
          case repeatedReduce new_arg of
            Nothing               -> Just (new_arg, co)
            Just (newer_arg, co') -> Just (newer_arg, FcCoTrans co co')

    reduceOrReflect ::
         RnMonoTy -> Maybe (RnMonoTy, FcCoercion) -> (RnMonoTy, FcCoercion)
    reduceOrReflect _ty (Just (new_ty, co)) = (new_ty,co)
    reduceOrReflect ty Nothing = (ty, FcCoRefl (elabMonoTy' ty))

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: MonadError CompileError m => FullTheory -> RnClsCt -> m ()
overlapCheck theory cls_ct@(ClsCt cls1 [ty1])
  -- We only care about the instance theory
 =
  case catMaybes (fmap overlaps (theory_inst theory)) of
    msg:_ -> tcFail msg
    []    -> return ()
  where
    overlaps (_ :| scheme@(CtrScheme _ _ (ClsCt cls2 [ty2])))
      | cls1 == cls2
      , Right {} <- unify [] [ty1 :~: ty2] =
        Just (text "overlapCheck:" $$ ppr cls_ct $$ ppr scheme)
      | otherwise = Nothing

-- * Constraint Entailment
-- ------------------------------------------------------------------------------

-- | Simplify the wanted type class constraints. Return the residual constraints
-- | and the dictionary substitution.
simplify :: [RnTyVar] -> ProgramTheory -> AnnClsCs -> TcM (AnnClsCs, FcTmSubst)
simplify _as _theory [] = return (mempty, mempty)
simplify as theory (ct:cs) =
  entail as theory ct >>= \case
    Nothing -> do
      (residual_cs, fc_tm_subst) <- simplify as theory cs
      return (ct:residual_cs, fc_tm_subst)
    Just (cs', fc_subst) -> do
      (residual_cs, fc_subst') <- simplify as theory $ cs' <> cs
      return (residual_cs, fc_subst' <> fc_subst)

-- | Entail a single type class constraint. Returns Nothing if nothing has been
-- | done. May produce additional class constraints.
entail :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (Maybe (AnnClsCs, FcTmSubst))
entail _untch [] _cls_ct = return Nothing
entail as ((d' :| CtrScheme bs cls_cs (ClsCt cls2 [ty2])):schemes) ct@(d :| ClsCt cls1 [ty1])
  | cls1 == cls2
  , Right ty_subst <- unify as [ty1 :~: ty2] = do
    (d''s, ann_cls_cs) <- annotateClsCs $ substInClsCs ty_subst cls_cs
    fc_subbed_bs <- mapM elabMonoTy . substInTyVars ty_subst $ labelOf bs
    let ev_subst =
          d |->
           foldl
             FcTmApp
             (foldl FcTmTyApp (FcTmVar d') fc_subbed_bs)
             (FcTmVar <$> d''s)
    return $ Just (ann_cls_cs, ev_subst)
  | otherwise = entail as schemes ct

-- | Returns the (transitive) super class constaints of the type class constraint
-- | using the super class theory.
closure :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (AnnClsCs, FcTmSubst)
closure untchs theory cls_ct = go theory cls_ct
  where
    go ((d_top :| CtrScheme alphas [ClsCt cls2 [ty2]] q):schemes) ct@(d :| ClsCt cls1 [ty1])
      | cls1 == cls2
      , Right ty_subst <- unify untchs [ty1 :~: ty2] = do
        d' <- freshDictVar
        let sub_q = substInClsCt ty_subst q
        fc_subbed_alphas <-
          mapM elabMonoTy . substInTyVars ty_subst $ labelOf alphas
        let ev_subst =
              d' |->
               FcTmApp
                 (foldl FcTmTyApp (FcTmVar d_top) fc_subbed_alphas)
                 (FcTmVar d)
        (cls_cs, ev_subst') <- go schemes ct
        (all_cs, ev_subst'') <- closureAll untchs theory (d' :| sub_q : cls_cs)
        return (d' :| sub_q : cls_cs <> all_cs, ev_subst <> ev_subst' <> ev_subst'')
      | otherwise = go schemes ct
    go [] _cls_ct = return (mempty, mempty)
    go _ _ =
      tcFail $
        text "closure" <+> colon <+>
          text "constraint scheme has too many implications"

closureAll :: [RnTyVar] -> ProgramTheory -> AnnClsCs -> TcM (AnnClsCs, FcTmSubst)
closureAll as theory cs =
  ((\(a, b) -> (mconcat a, mconcat b)) . unzip) <$> mapM (closure as theory) cs

-- | Determinacy relation
determinacy :: [RnTyVar] -> RnClsCs -> TcM HsTySubst
determinacy as cls_cs = go cls_cs mempty
  where
    go cs ty_subst = do
      (residual_cs, new_substs) <-
        partitionEithers <$> mapM (det_step ty_subst) cs
      if null new_substs then return ty_subst else
        go residual_cs (ty_subst <> mconcat new_substs)

    det_step ty_subst ct@(ClsCt cls tys) = do
      as' <- lookupClsParams cls
      fds <- lookupClsFundeps cls
      fd_fams <- lookupClsFDFams cls
      let cls_var_subst = buildSubst $ zip as' tys
      new_subst <- fmap mconcat $
        forM (zip fds fd_fams) $ \(Fundep bs b0, fam) -> do
          let (t0:ts) = substInMonoTy cls_var_subst . TyVar <$> (b0 : bs)
          let refined_ts = substInMonoTy ty_subst <$> ts
          let as_dom = as <> substDom ty_subst
          if any (`elem` as_dom) (ftyvsOf t0) ||
             not (all (`elem` as_dom) $ ftyvsOf ts)
            then return mempty
            else mconcat . map (\(fv, proj) -> fv |-> proj (TyFam fam refined_ts)) <$>
                 projection t0
      return $ if nullSubst new_subst then Left ct else Right new_subst

-- | Gather type variables and compute their corresponding projection function
projection :: RnMonoTy -> TcM [(RnTyVar, RnMonoTy -> RnMonoTy)]
projection = go id
  where
    go f ty =
      case ty of
        app@(TyApp _ _) -> do
          (tc, tys) <- destructTyApp app
          ty_fams <- lookupTyConProj tc
          concat <$>
            mapM
              (\(ty_fam, app_ty) -> go (\x -> f (TyFam ty_fam [x])) app_ty)
              (zip ty_fams tys)
        TyVar a   -> return [(a, f)]
        TyCon _   -> return []
        TyFam _ _ -> tf_error

    destructTyApp (TyApp ty1 ty2) = do
      (tc, tys) <- destructTyApp ty1
      return (tc, tys ++ [ty2])
    destructTyApp (TyCon tc) = return (tc, [])
    destructTyApp TyFam {} = tf_error
    destructTyApp (TyVar _a) =
      throwErrorM $
      text "projection" <+>
      colon <+> text "Type variable applications are not yet supported"

    tf_error =
      throwErrorM $
      text "projection" <+> colon <+> text "encountered type family"

dictDestruction :: AnnClsCs -> TcM (MatchCtx)
dictDestruction [] = return MCtxHole
dictDestruction ((d :| ClsCt cls tys):cs) = do
  dc <- lookupClsDataCon cls
  tc <- lookupClsTyCon cls
  e2 <- dictDestruction (undefined ++ cs)
  let pat = FcConPat dc [] [] []
  return $ MCtxCase d pat e2

-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl ::
     RnClsDecl
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
    dbinds <- annCtsToTmBinds ann_cs

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

  -- TODO old way of dealing with superclasses
  (sc_schemes, sc_decls) <- fmap unzip $ forM (zip [0..] rn_cs) $ \(i,sc_ct) -> do
    d  <- freshDictVar -- For the declaration
    da <- freshDictVar -- For the input dictionary

    let cls_head  = ClsCt cls (TyVar <$> as) -- TC   as
    fc_cls_head  <- elabClsCt cls_head       -- T_TC as

    -- forall a. TC a => SC
    let scheme = CtrScheme (as |: (kindOf <$> as)) [cls_head] sc_ct
    -- forall a. T_TC a -> upsilon_SC
    fc_scheme <- elabScheme scheme

    -- n+1 fresh variables
    xs <- replicateM (length rn_cs + 1) freshFcTmVar

    let fc_tm =
          fcTmTyAbs fc_as $
          FcTmAbs da fc_cls_head $
          FcTmCase
            (FcTmVar da)
            [ FcAlt
                (FcConPat dc [] [] (xs |: (fc_sc_tys ++ [fc_method_ty])))
                (FcTmVar (xs !! i))
            ]

    let proj = FcValBind d fc_scheme fc_tm

    return (d :| scheme, proj)

  return (fc_fam_decls, fc_data_decl, fc_val_bind:sc_decls, sc_schemes, ty_ctx)

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
annCtsToTmBinds :: AnnClsCs -> TcM [(FcTmVar, FcType)]
annCtsToTmBinds = mapM (\(d :| ct) -> (,) d <$> elabClsCt ct)

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

-- | Elaborate a class instance. Take the program theory also as input and return
--   a) The dictionary transformer implementation
--   b) The extended program theory
elabInsDecl :: FullTheory -> RnInsDecl -> TcM (FcValBind, FullTheory)
elabInsDecl theory (InsD as ins_cs cls [typat] method method_tm) = do
  let ty = hsTyPatToMonoTy typat
  let bs      = as
  let fc_bs   = map (rnTyVarToFcTyVar . labelOf) bs
  let head_ct = ClsCt cls [ty]

  -- Ensure the instance does not overlap
  overlapCheck theory head_ct

  -- Create the instance constraint scheme
  ins_d <- freshDictVar
  ins_scheme <- fmap (ins_d :|) $ freshenLclBndrs $ CtrScheme bs ins_cs head_ct

  --  Generate fresh dictionary variables for the instance context
  ann_ins_cs <- snd <$> annotateClsCs ins_cs
  (closure_cs, closure_ev_subst) <- closureAll
                                      (labelOf bs)
                                      (theory_super theory)
                                       ann_ins_cs
  let ann_ins_schemes = (fmap . fmap) (CtrScheme [] []) (closure_cs <> ann_ins_cs)

  -- The extended program theory
  let ext_theory = theory `ftExtendInst` [ins_scheme]

  --  The local program theory
  let local_theory = ext_theory `ftExtendLocal` ann_ins_schemes

  -- Create the dictionary transformer type
  dtrans_ty <- do
    fc_head_ty <- extendTcCtxTysM (labelOf bs) (wfElabClsCt head_ct)
    fc_ins_cs <- extendTcCtxTysM (labelOf bs) (wfElabClsCs ins_cs)
    return $ fcTyAbs fc_bs $ fcTyArr fc_ins_cs fc_head_ty

  -- Elaborate the method implementation
  fc_method_tm <- do
    expected_method_ty <- instMethodTy ty <$> lookupCtxM method
    elabTermWithSig (labelOf bs) local_theory method_tm expected_method_ty

  -- Entail the superclass constraints
  fc_super_tms <- do
    a <- lookupClsParam cls
    (ds, super_cs) <- substVar a ty <$>
                        lookupClsSuper cls >>= annotateClsCs

    (residual_cs, ev_subst) <- simplify
                                 (labelOf bs)
                                 (ftDropSuper local_theory) -- TODO apearantly these should not include the instance scheme
                                  super_cs

    unless (null residual_cs) $
      tcFail (text "Failed to resolve superclass constraints" <+>
                   colon <+>
                   ppr residual_cs $$ text "From" <+> colon <+> ppr local_theory)

    return (map (substFcTmInTm ev_subst . FcTmVar) ds)

  -- The full implementation of the dictionary transformer
  fc_dict_transformer <- do
    binds <- annCtsToTmBinds ann_ins_cs
    dc    <- lookupClsDataCon cls
    fc_ty <- elabMonoTy ty
    return $ substFcTmInTm closure_ev_subst $
      fcTmTyAbs fc_bs $
        fcTmAbs binds $
           fcDataConApp dc fc_ty (fc_super_tms ++ [fc_method_tm])

  -- Resulting dictionary transformer
  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer

  return (fc_val_bind, ext_theory)

-- | Instantiate a method type for a particular instance
instMethodTy :: RnMonoTy -> RnPolyTy -> RnPolyTy
instMethodTy typat poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    ((a :| _kind):as,_c:cs,ty) = destructPolyTy poly_ty
    subst      = a |-> typat
    new_as     = as
    new_cs     = substInClsCs  subst cs
    new_ty     = substInMonoTy subst ty

-- | Elaborate a term with an explicit type signature (method implementation).
-- This involves both inference and type subsumption.
elabTermWithSig :: [RnTyVar] -> FullTheory -> RnTerm -> RnPolyTy -> TcM FcTerm
elabTermWithSig untch theory tm poly_ty = do
  let (as, cs, ty) = destructPolyTy poly_ty
  let fc_as = map rnTyVarToFcTyVar (labelOf as)

  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  -- Generate fresh dictionary variables for the given constraints
  given_ccs <- snd <$> annotateClsCs cs
  dbinds <- annCtsToTmBinds given_ccs
  (super_cs, closure_ev_subst) <- closureAll untch (theory_super theory) given_ccs
  let given_schemes = (fmap . fmap) (CtrScheme [] []) (super_cs <> given_ccs)

  -- Resolve all the wanted constraints
  let untouchables = nub (untch ++ map labelOf as)
  ty_subst <- unify untouchables $ (dropLabel wanted_eqs) ++ [mono_ty :~: ty]
  let local_theory = ftDropSuper theory <> given_schemes
  let wanted = substInAnnClsCs ty_subst wanted_ccs

   -- rightEntailsRec untouchables local_theory wanted
  (residual_cs, ev_subst) <- simplify untouchables local_theory wanted

  -- Ensure that the constraints are completely resolved
  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve constraints" <+>
       colon <+> ppr residual_cs $$ text "From" <+> colon <+> ppr theory
       $$ text "Wanted" <+> colon <+> ppr wanted)
  fc_subst <- elabHsTySubst ty_subst

  -- Generate the resulting System F term
  return $
    fcTmTyAbs fc_as $
    fcTmAbs dbinds $
      substFcTmInTm (closure_ev_subst <> ev_subst) $
        substFcTyInTm fc_subst fc_tm

-- | Convert a source type substitution to a System F type substitution
elabHsTySubst :: HsTySubst -> TcM FcTySubst
elabHsTySubst = mapSubM (return . rnTyVarToFcTyVar) elabMonoTy

-- * Type Inference With Constraint Simplification
-- ------------------------------------------------------------------------------

elabTermSimpl :: ProgramTheory -> RnTerm -> TcM (RnPolyTy, FcTerm)
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  -- Simplify as much as you can
  -- Solve the needed equalities first
  ty_subst <- unify mempty (dropLabel wanted_eqs)

  let refined_wanted_ccs = substInAnnClsCs      ty_subst wanted_ccs             -- refine the wanted class constraints
  let refined_mono_ty    = substInMonoTy        ty_subst mono_ty                -- refine the monotype
  -- refine the term
  refined_fc_tm <- flip substFcTyInTm fc_tm <$> elabHsTySubst ty_subst

  let untouchables = nub (ftyvsOf refined_wanted_ccs ++ ftyvsOf refined_mono_ty)

  (residual_cs, ev_subst) <- simplify untouchables theory refined_wanted_ccs

  -- Generalize the type
  let new_mono_ty = refined_mono_ty
  let new_cs      = map dropLabel residual_cs
  let new_as      = untouchables
  let gen_ty      = constructPolyTy (map (\a -> a :| kindOf a) new_as, new_cs, new_mono_ty)

  -- Elaborate the term
  let fc_as = map rnTyVarToFcTyVar new_as
  dbinds   <- annCtsToTmBinds residual_cs
  let full_fc_tm = fcTmTyAbs fc_as $
                     fcTmAbs dbinds $
                       substFcTmInTm ev_subst refined_fc_tm

  return (gen_ty, full_fc_tm)

-- * Value Binding Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a top-level value binding
elabValBind :: FullTheory -> RnValBind -> TcM (FcValBind, TcCtx)
elabValBind theory (ValBind a m_ty tm) = do
  (ty,fc_tm) <- case m_ty of
    Nothing -> elabTermSimpl (ftDropSuper theory) tm
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
elabProgram :: FullTheory -> RnProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnPolyTy        {- Term type (MonoTy?)      -}
                   , FullTheory )    {- Final program theory     -}
-- Elaborate the program expression
elabProgram theory (PgmExp tm) = do
  (ty, fc_tm) <- elabTermSimpl (ftDropSuper theory) tm
  return (FcPgmTerm fc_tm, ty, theory) -- GEORGE: You should actually return the ones we have accumulated.

-- Elaborate a class declaration
elabProgram theory (PgmCls cls_decl pgm) = do
  (fc_fam_decls, fc_data_decl, fc_val_binds, ext_theory, ext_ty_env) <-
    elabClsDecl cls_decl
  (fc_pgm, ty, final_theory) <-
    setCtxM ext_ty_env (elabProgram (theory `ftExtendSuper` ext_theory) pgm)
  let fc_pgm_data_val_decls =
        FcPgmDataDecl
          fc_data_decl
             (foldl (flip FcPgmValDecl) fc_pgm fc_val_binds)
  let fc_program = foldr FcPgmFamDecl fc_pgm_data_val_decls fc_fam_decls
  return (fc_program, ty, final_theory)

-- | Elaborate a class instance
elabProgram theory (PgmInst ins_decl pgm) = do
  (fc_val_bind, ext_theory) <- elabInsDecl theory ins_decl
  (fc_pgm, ty, final_theory) <- elabProgram ext_theory pgm
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
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
  -> Either CompileError ( (((FcProgram, RnPolyTy, FullTheory)), UniqueSupply)
                         , TcEnv)
hsElaborate rn_gbl_env us pgm = runExcept
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT tc_init_ctx
                              $ flip runUniqueSupplyT us
                              $ markTcError
                              $ do buildInitTcEnv pgm rn_gbl_env
                                   elabProgram tc_init_theory pgm
  where
    tc_init_theory  = FT mempty mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty mempty

tcFail :: MonadError CompileError m => Doc -> m a
tcFail = throwError . CompileError HsTypeChecker

markTcError :: MonadError CompileError m => m a -> m a
markTcError = markErrorPhase HsTypeChecker
