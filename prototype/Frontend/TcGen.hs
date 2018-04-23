{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Frontend.TcGen where

import           Frontend.FunDep
import           Frontend.HsTypes
import           Frontend.TcMonad
import           Frontend.TcType

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.Ctx
import           Utils.Errors
import           Utils.Kind
import           Utils.PrettyPrint    hiding ((<>))
import           Utils.Substitution
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List            (intersect, (\\))
import           Data.Monoid          ((<>))

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

  -- TODO fix for superclasses
  fd_eq_cs <- liftGenM . fmap concat $
    forM ann_cs $ \(_d :| ClsCt cls tys) -> do
      fds <- lookupClsFundeps cls
      fams <- lookupClsFDFams cls
      as' <- lookupClsParams cls
      let fd_subst = buildSubst (zipExact as' tys)
      forM (zipExact fams fds) $ \(fam, Fundep ais ai0) -> do
        c <- freshFcCoVar
        return $
          c :| TyFam fam (substInMonoTy fd_subst . TyVar <$> ais) :~:
          substInMonoTy fd_subst (TyVar ai0)
  storeEqCs  fd_eq_cs

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
