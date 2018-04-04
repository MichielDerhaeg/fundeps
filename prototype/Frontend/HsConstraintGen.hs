{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Frontend.HsConstraintGen where

import           Frontend.HsTcMonad
import           Frontend.HsTypes

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.Ctx
import           Utils.Errors
import           Utils.FreeVars
import           Utils.Kind
import           Utils.PrettyPrint    hiding ((<>))
import           Utils.Substitution
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Either          (partitionEithers)
import           Data.List            (intersect, (\\))

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
elabMonoTy :: RnMonoTy -> FcType
elabMonoTy (TyCon tc)      = FcTyCon $ rnTyConToFcTyCon tc
elabMonoTy (TyApp ty1 ty2) = FcTyApp (elabMonoTy ty1) (elabMonoTy ty2)
elabMonoTy (TyVar v)       = rnTyVarToFcType v
elabMonoTy (TyFam f tys)   = FcTyFam (rnTyFamToFcFam f) (elabMonoTy <$> tys)

-- | Elaborate a class constaint
elabClsCt :: RnClsCt -> TcM FcType
elabClsCt (ClsCt cls tys) = do
  fc_tc <- lookupClsTyCon cls
  return $ fcTyApp (FcTyCon fc_tc) (elabMonoTy <$> tys)

-- | Elaborate class constraints
elabClsCs :: RnClsCs -> TcM [FcType]
elabClsCs = mapM elabClsCt

-- | Elaborate an equality constraint
elabEqCt :: EqCt -> FcProp
elabEqCt (ty1 :~: ty2) = FcProp (elabMonoTy ty1) (elabMonoTy ty2)

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
elabQualTy (QMono ty) = return $ elabMonoTy ty

-- | Convert a source type substitution to a System F type substitution
elabHsTySubst :: HsTySubst -> FcTySubst
elabHsTySubst =  mapSub rnTyVarToFcTyVar elabMonoTy

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
annotateClsCs :: MonadUnique m => RnClsCs -> m ([DictVar], AnnClsCs)
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
  return (a, fc_tm)

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
  let fc_bs = (elabMonoTy . substInTyVar subst) <$> bs'
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

-- | Elaborate a case expression
elabTmCase :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase scr alts = do
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
      let fc_tys = elabMonoTy <$> arg_tys'
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

-- * Determinacy
-- ------------------------------------------------------------------------------

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
      let cls_var_subst = buildSubst $ zipExact as' tys
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
