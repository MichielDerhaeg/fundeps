{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Frontend.HsEntail where

import           Backend.FcTypes
import           Frontend.HsTypeChecker
import           Frontend.HsTypes

import           Utils.Annotated
import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint  hiding ((<>), empty)
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var

import           Control.Applicative
import           Control.Arrow             (first, second)
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Monoid

type WantedEqCt = Ann FcCoVar EqCt

type WantedClsCt = Ann DictVar RnClsCt

data WantedCt
  = WantedEqCt WantedEqCt
  | WantedClsCt WantedClsCt

type WantedCs = [WantedCt]

type GivenEqCt = Ann FcCoercion EqCt

type GivenClsCt = Ann FcTerm RnClsCt

data GivenCt
  = GivenEqCt GivenEqCt
  | GivenClsCt GivenClsCt

type GivenCs = [GivenCt]

type EntailM = StateT EntailState TcM

runEntailT :: [RnTyVar] -> EntailM a -> TcM (a, EntailState)
runEntailT untchs = flip runStateT init_entail
  where
    init_entail = EntailState untchs mempty mempty mempty

data EntailState = EntailState
  { untouchables  :: [RnTyVar]
  , flat_ty_subst :: HsTySubst
  , flat_ev_subst :: EvSubst
  , solv_ev_subst :: EvSubst
  }

getUntchs :: MonadState EntailState m => m [RnTyVar]
getUntchs = gets untouchables

addUntch :: MonadState EntailState m => RnTyVar -> m ()
addUntch a = modify $ \s -> s { untouchables = a : untouchables s }

addFlatTySubst :: MonadState EntailState m => HsTySubst -> m ()
addFlatTySubst subst =
  modify $ \s -> s {flat_ty_subst = flat_ty_subst s <> subst}

addFlatEvSubst :: MonadState EntailState m => EvSubst -> m ()
addFlatEvSubst subst =
  modify $ \s -> s {flat_ev_subst = flat_ev_subst s <> subst}

addSolvEvSubst :: MonadState EntailState m => EvSubst -> m ()
addSolvEvSubst subst =
  modify $ \s -> s {solv_ev_subst = solv_ev_subst s <> subst}

addSolvCoSubst :: MonadState EntailState m => FcCoSubst -> m ()
addSolvCoSubst = addSolvEvSubst . coToEvSubst

addSolvTmSubst :: MonadState EntailState m => FcTmSubst -> m ()
addSolvTmSubst = addSolvEvSubst . tmToEvSubst

-- | Substitute an equality within a type and generate a coercion.
-- This is weird, type type signature could be more precise.
-- Instead of returning what we passed and throwing it away.
coTy :: FcCoercion -> RnTyVar -> RnMonoTy -> RnMonoTy -> (FcCoercion, RnMonoTy)
coTy co a ty b_ty@(TyVar b)
  | a == b = (co, ty)
  | otherwise = (FcCoRefl (elabMonoTy b_ty), b_ty)
coTy co a ty (TyApp ty1 ty2) =
  (FcCoApp co1' co2', substVar a ty (TyApp ty1 ty2))
  where
    (co1' , _) = coTy co a ty ty1
    (co2' , _) = coTy co a ty ty2
coTy _co _a _ty tc@(TyCon _tc) =
  (FcCoRefl (elabMonoTy tc), tc)
coTy co a ty tyfam@(TyFam f tys) =
  (FcCoFam (rnTyFamToFcFam f) crcs, substVar a ty tyfam)
  where
    crcs = fst . coTy co a ty <$> tys

coCt ::
     (MonadState TcEnv m, MonadError CompileError m)
  => FcCoercion
  -> RnTyVar
  -> RnMonoTy
  -> RnClsCt
  -> m (FcCoercion, RnClsCt)
coCt co a ty ct@(ClsCt cls tys) = do
  cls_tc <- lookupClsTyCon cls
  return (fcCoApp (FcCoRefl (FcTyCon cls_tc)) crcs, substVar a ty ct)
  where
    crcs = fst . coTy co a ty <$> tys

fcCoApp :: FcCoercion -> [FcCoercion] -> FcCoercion -- TODO move to FcTypes
fcCoApp = foldl FcCoApp

canCheckGivens :: (MonadError CompileError m, MonadState EntailState m) => GivenCs -> m ()
canCheckGivens = mapM_ canCheckGiven
  where
    canCheckGiven (GivenEqCt  (_ :| ct)) = canCheckEqCt  ct
    canCheckGiven (GivenClsCt (_ :| ct)) = canCheckClsCt ct

canCheckWanteds :: (MonadError CompileError m, MonadState EntailState m) => WantedCs -> m ()
canCheckWanteds = mapM_ canCheckWanted
  where
    canCheckWanted (WantedEqCt  (_ :| ct)) = canCheckEqCt  ct
    canCheckWanted (WantedClsCt (_ :| ct)) = canCheckClsCt ct

canCheckEqCt :: (MonadError CompileError m, MonadState EntailState m) => EqCt -> m ()
canCheckEqCt ct@(TyVar a :~: ty) = do
  untchs <- getUntchs
  unless
    (isOrphan ty && a `notElem` ftyvsOf ty && smallerThan untchs (TyVar a) ty) $
    canonFail ct
canCheckEqCt ct@(TyFam _f tys :~: ty) =
  unless (all isOrphan (ty : tys)) $ canonFail ct
canCheckEqCt ct = canonFail ct

canCheckClsCt :: (MonadError CompileError m, MonadState EntailState m) => RnClsCt -> m ()
canCheckClsCt ct@(ClsCt _cls tys) = unless (all isOrphan tys) $ canonFail ct

canonFail :: (PrettyPrint ct, MonadError CompileError m) => ct -> m ()
canonFail ct =
  throwErrorM $
  text "Canonicity check failed on constraint" <+> colon <+> ppr ct

smallerThan :: [RnTyVar] -> RnMonoTy -> RnMonoTy -> Bool
smallerThan untchs = go
  where
    -- F tys < ty when ty /= G tys'
    go TyFam {} TyVar {} = True
    go TyFam {} TyApp {} = True
    go TyFam {} TyCon {} = True

    -- alpha < b
    go (TyVar a) (TyVar b) = a `notElem` untchs || a <= b

    -- tv < Xi
    go TyVar {} ty = isOrphan ty

    go _ _ = False

-- | Checks if the type contains no type families
isOrphan :: RnMonoTy -> Bool
isOrphan TyCon {} = True
isOrphan (TyApp ty1 ty2) = isOrphan ty1 && isOrphan ty2
isOrphan TyVar {} = True
isOrphan TyFam {} = False

interactWanted :: WantedCt -> WantedCt -> MaybeT EntailM WantedCs
interactWanted (WantedEqCt (c1 :| ct1@(TyVar a :~: ty1)))
               (WantedEqCt (c2 :|      TyVar b :~: ty2))
  -- EQSAME
  | a == b = do
    c2' <- freshFcCoVar
    addSolvCoSubst (c2 |-> FcCoTrans (FcCoVar c1) (FcCoVar c2'))
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| ty1 :~: ty2] )
  -- EQDIFF
  | a `elem` ftyvsOf ty2
  , let (co, sub_ty2) = coTy (FcCoVar c1) a ty1 ty2 = do
    c2' <- freshFcCoVar
    addSolvCoSubst (c2 |-> FcCoTrans (FcCoVar c2') (FcCoSym co))
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| TyVar b :~: sub_ty2] )
interactWanted (WantedEqCt (c1 :| ct1@(TyVar     a :~:  ty1)))
               (WantedEqCt (c2 :|     (TyFam f tys :~:  ty2)))
  -- EQFEQ
  | a `elem` ftyvsOf (ty2 : tys)
  , let (co1, sub_tyfam) = coTy (FcCoVar c1) a ty1 (TyFam f tys)
  , let (co2, sub_ty2)   = coTy (FcCoVar c1) a ty1 ty2 = do
    c2' <- freshFcCoVar
    addSolvCoSubst (c2 |-> FcCoTrans co1 (FcCoTrans (FcCoVar c2') (FcCoSym co2)))
    return
      ( WantedEqCt <$> [ c1 :| ct1, c2' :| sub_tyfam :~: sub_ty2] )
interactWanted (WantedEqCt  (c :| ct1@(TyVar a :~: ty)))
               (WantedClsCt (d :| ct2@(ClsCt _cls tys)))
  -- EQDICT
  | a `elem` ftyvsOf tys = do
    (co, sub_cls) <- lift . lift $ coCt (FcCoVar c) a ty ct2
    d' <- freshDictVar
    addSolvTmSubst (d |-> FcTmCast (FcTmVar d') (FcCoSym co))
    return
      [WantedEqCt (c :| ct1), WantedClsCt (d' :| sub_cls)]
interactWanted (WantedEqCt (c1 :| ct1@(TyFam _f1 _tys1 :~: ty1)))
               (WantedEqCt (c2 :|     (TyFam _f2 _tys2 :~: ty2))) = do
  -- FEQFEQ
    c2' <- freshFcCoVar
    addSolvCoSubst (c2 |-> FcCoTrans (FcCoVar c1) (FcCoVar c2'))
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| ty1 :~: ty2] )
interactWanted (WantedClsCt (d1 :| ClsCt cls1 tys1))
               (WantedClsCt (d2 :| ClsCt cls2 tys2))
  -- DDICT
  | and (zipWithExact eqMonoTy tys1 tys2), cls1 == cls2 = do
    addSolvTmSubst (d2 |-> FcTmVar d1)
    return
      [WantedClsCt (d1 :| ClsCt cls1 tys1)]
interactWanted _ _ = empty

-- TODO always return first total constraint? order important?
interactGiven :: GivenCt -> GivenCt -> MaybeT EntailM GivenCs
interactGiven (GivenEqCt (co1 :| ct1@(TyVar a :~: ty1)))
              (GivenEqCt (co2 :|      TyVar b :~: ty2))
  -- EQSAME
  | a == b =
  return
    ( GivenEqCt <$> [co1 :| ct1
    , FcCoTrans (FcCoSym co1) co2 :| (ty1 :~: ty2)])
  -- EQDIFF
  | a `elem` ftyvsOf ty2
  , let (co, sub_ty) = coTy co1 a ty1 ty2 =
  return
    ( GivenEqCt <$> [co1 :| ct1
    , FcCoTrans co2 co :| (TyVar b :~: sub_ty)])
interactGiven (GivenEqCt (co1 :|  ct1@(TyVar a       :~: ty1)))
              (GivenEqCt (co2 :| (fam@(TyFam _f tys) :~: ty2)))
  -- EQFEQ
  | a `elem` ftyvsOf tys
  , let (co1', sub_fam) = coTy co1 a ty1 fam
  , let (co2', sub_ty2) = coTy co1 a ty1 ty2 =
  return ( GivenEqCt <$> [co1 :| ct1
         , FcCoTrans (FcCoSym co1') (FcCoTrans co2 co2') :| (sub_fam :~: sub_ty2)])
interactGiven (GivenEqCt  (co :| ct1@(TyVar a :~: ty)))
              (GivenClsCt (tm :| ct2@(ClsCt _cls tys)))
  -- EQDICT
  | a `elem` ftyvsOf tys = do
  (co', sub_cls) <- lift . lift $ coCt co a ty ct2
  return [ GivenEqCt (co :| ct1)
         , GivenClsCt (FcTmCast tm co' :| sub_cls)]
interactGiven (GivenEqCt (co1 :| ct1@(fam1@TyFam {} :~: ty1)))
              (GivenEqCt (co2 :|     (fam2@TyFam {} :~: ty2)))
  -- FEQFEQ
  | eqMonoTy fam1 fam2 =
  return ( GivenEqCt <$> [co1 :| ct1
         , FcCoTrans (FcCoSym co1) co2 :| (ty1 :~: ty2)])
interactGiven (GivenClsCt ( tm1 :|  ct1@(ClsCt cls1 tys1)))
              (GivenClsCt (_tm2 :| _ct2@(ClsCt cls2 tys2)))
  -- DDICT
  | cls1 == cls2, and (zipWithExact eqMonoTy tys1 tys2) =
  return [GivenClsCt (tm1 :| ct1)] -- TODO tm1 right?
interactGiven _ _ = empty

-- TODO shouls not consume Given input?
simplify :: GivenCt -> WantedCt -> MaybeT EntailM WantedCs
simplify (GivenEqCt  (co :| TyVar a :~: ty1))
         (WantedEqCt (c  :| TyVar b :~: ty2))
  -- SEQSAME
  | a == b = do
  c' <- freshFcCoVar
  addSolvCoSubst (c |-> FcCoTrans co (FcCoVar c'))
  return [WantedEqCt (c' :| (ty1 :~: ty2))]
  -- SEQDIFF
  | a `elem` ftyvsOf ty2
  , let (co', sub_ty2) = coTy co a ty1 ty2 = do
  c' <- freshFcCoVar
  addSolvCoSubst (c |-> FcCoTrans (FcCoVar c') (FcCoSym co'))
  return [WantedEqCt (c' :| (TyVar b :~: sub_ty2))]
simplify (GivenEqCt  (co :| TyVar a            :~: ty1))
         (WantedEqCt (c  :| fam@(TyFam _f tys) :~: ty2))
  -- SEQFEQ
  | a `elem` ftyvsOf tys
  , let (co', sub_fam) = coTy co a ty1 fam = do
  c' <- freshFcCoVar
  addSolvCoSubst (c |-> FcCoTrans co' (FcCoVar c'))
  return [WantedEqCt (c' :| (sub_fam :~: ty2))]
simplify (GivenEqCt   (co :|     (TyVar a :~: ty1)))
         (WantedClsCt (d  :| ct2@(ClsCt _cls  tys)))
  -- SEQDICT
  | a `elem` ftyvsOf tys = do
  (co', sub_cls) <- lift . lift $ coCt co a ty1 ct2
  d' <- freshDictVar
  addSolvTmSubst (d |-> FcTmCast (FcTmVar d') (FcCoSym co'))
  return [WantedClsCt (d' :| sub_cls)]
simplify (GivenEqCt   (co :| (fam1@TyFam {} :~: ty1)))
         (WantedEqCt  (c  :| (fam2@TyFam {} :~: ty2)))
  -- SFEQFEQ
  | eqMonoTy fam1 fam2 = do
  c' <- freshFcCoVar
  addSolvCoSubst (c |-> FcCoTrans co (FcCoVar c'))
  return [WantedEqCt (c' :| (ty1 :~: ty2))]
simplify (GivenClsCt  (tm :| ClsCt cls1 tys1))
         (WantedClsCt (d  :| ClsCt cls2 tys2))
  | cls1 == cls2, and (zipWithExact eqMonoTy tys1 tys2) = do
  addSolvTmSubst (d |-> tm)
  return mempty
simplify _ _ = empty

canonicalizeWanted :: WantedCt -> MaybeT EntailM WantedCs
canonicalizeWanted (WantedEqCt (c :| ct)) = do
  untchs <- getUntchs
  fmap WantedEqCt <$> go untchs ct
  where
    -- REFLW
    go _ (ty1 :~: ty2)
      | eqMonoTy ty1 ty2 = do
        addSolvCoSubst $ c |-> FcCoRefl (elabMonoTy ty1)
        return mempty
    -- TYAPPW
    go _ (TyApp ty1 ty2 :~: TyApp ty3 ty4) = do
      [c1, c2] <- genFreshCoVars 2
      addSolvCoSubst $ c |-> FcCoApp (FcCoVar c1) (FcCoVar c2)
      return [c1 :| (ty1 :~: ty3), c2 :| (ty2 :~: ty4)]
    -- FAILDECW
    go _ (TyCon tc1 :~: TyCon tc2)
      | tc1 /= tc2 = throwErrorM $ text "TODO"
    -- OCCCHECKW
    go _ (TyVar a :~: ty)
      | a `elem` ftyvsOf ty
      , not (eqMonoTy (TyVar a) ty) = throwErrorM $ text "TODO occurscheck"
    -- ORIENTW
    go untchs (ty1 :~: ty2)
      | smallerThan untchs ty2 ty1 = do
        c' <- freshFcCoVar
        addSolvCoSubst $ c |-> FcCoSym (FcCoVar c')
        return [c' :| (ty2 :~: ty1)]
    -- FFLATWL
    go _ (search_ty :~: ty)
      | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamFam search_ty = do
        [c1, c2] <- genFreshCoVars 2
        beta     <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
        let ctx_beta = applyFamCtx ctx (TyVar beta)
        let (co, _ty) =
              coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        addSolvCoSubst $ c |-> FcCoTrans (FcCoSym co) (FcCoVar c2)
        return [c1 :| (fam_ty :~: TyVar beta), c2 :| (ctx_beta :~: ty)]
    -- FFLATWR
    go _ (ty :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f1 _)) <- nestedFamTy search_ty
      , TyFam {} <- ty = do
        [c1, c2] <- genFreshCoVars 2
        beta <- lift . lift $ lookupTyFamKind f1 >>= freshRnTyVar
        let ctx_beta = applyTyCtx ctx (TyVar beta)
        let (co, _) = coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        addSolvCoSubst $ c |-> FcCoTrans (FcCoVar c2) co
        return [c1 :| (fam_ty :~: TyVar beta), c2 :| (ty :~: ctx_beta)]
    -- TODO merge with above somehow
    go _ (ty@TyVar {} :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f1 _)) <- nestedFamTy search_ty = do
        [c1, c2] <- genFreshCoVars 2
        beta <- lift . lift $ lookupTyFamKind f1 >>= freshRnTyVar
        let ctx_beta = applyTyCtx ctx (TyVar beta)
        let (co, _) = coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        addSolvCoSubst $ c |-> FcCoTrans (FcCoVar c2) co
        return [c1 :| (fam_ty :~: TyVar beta), c2 :| (ty :~: ctx_beta)]
    go _ _ = empty
canonicalizeWanted (WantedClsCt (d :| cls_ct))
  -- DFLATW
  | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamCls cls_ct = do
    c' <- freshFcCoVar
    d' <- freshDictVar
    beta <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
    let ctx_beta    = applyClsCtx ctx (TyVar beta)
    (co, _ty) <- lift . lift $ coCt (FcCoSym (FcCoVar c')) beta fam_ty ctx_beta
    addSolvTmSubst (d |-> FcTmCast (FcTmVar d') co)
    return
      [WantedEqCt (c' :| (fam_ty :~: TyVar beta)), WantedClsCt (d' :| ctx_beta)]
canonicalizeWanted _ = empty

canonicalizeGiven :: GivenCt -> MaybeT EntailM GivenCs
canonicalizeGiven (GivenEqCt (co :| ct)) = do
  untchs <- getUntchs
  fmap GivenEqCt <$> go untchs ct
  where
    -- REFLG
    go _ (ty1 :~: ty2)
      | eqMonoTy ty1 ty2 = return mempty
    -- TYAPPG
    go _ (TyApp ty1 ty2 :~: TyApp ty3 ty4) =
      return [FcCoLeft co :| ty1 :~: ty3, FcCoRight co :| ty2 :~: ty4]
    -- FAILDECG
    go _ (TyCon tc1 :~: TyCon tc2)
      | tc1 /= tc2 = throwErrorM $ text "TODO"
    -- OCCCHECKG
    go _ (TyVar a :~: ty)
      | a `elem` ftyvsOf ty, not (eqMonoTy (TyVar a) ty) = throwErrorM $ text "TODO"
    -- ORIENTG
    go untchs (ty1 :~: ty2)
      | smallerThan untchs ty2 ty1 = return [FcCoSym co :| ty2 :~: ty1]
    -- FFLATGL
    go _ (search_ty :~: ty)
      | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamFam search_ty = do
        beta <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
        [c1, c2] <- genFreshCoVars 2
        addUntch beta
        addFlatTySubst $ beta |-> fam_ty
        addFlatEvSubst . coToEvSubst $
          c1 |-> co <> c2 |-> FcCoRefl (elabMonoTy fam_ty)
        return
          [ FcCoVar c1 :| applyFamCtx ctx (TyVar beta) :~: ty
          , FcCoVar c2 :| fam_ty :~: TyVar beta
          ]
    -- FFLATGR
    go _ (ty@(TyFam f' _) :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f _)) <- nestedFamTy search_ty
      , f == f' = do
        beta <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
        [c1, c2] <- genFreshCoVars 2
        addUntch beta
        addFlatTySubst $ beta |-> fam_ty
        addFlatEvSubst . coToEvSubst $
          c1 |-> co <> c2 |-> FcCoRefl (elabMonoTy fam_ty)
        return
          [ FcCoVar c1 :| ty :~: applyTyCtx ctx (TyVar beta)
          , FcCoVar c2 :| fam_ty :~: TyVar beta
          ]
    -- TODO unduplicate
    go _ (ty@TyVar {} :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamTy search_ty = do
        beta <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
        [c1, c2] <- genFreshCoVars 2
        addUntch beta
        addFlatTySubst $ beta |-> fam_ty
        addFlatEvSubst . coToEvSubst $
          c1 |-> co <> c2 |-> FcCoRefl (elabMonoTy fam_ty)
        return
          [ FcCoVar c1 :| ty :~: applyTyCtx ctx (TyVar beta)
          , FcCoVar c2 :| fam_ty :~: TyVar beta
          ]
    go _ _ = empty
canonicalizeGiven (GivenClsCt (tm :| cls_ct))
  -- DFLATG
  | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamCls cls_ct = do
    beta <- lift . lift $ lookupTyFamKind f >>= freshRnTyVar
    c <- freshFcCoVar
    d <- freshDictVar
    addUntch beta
    addFlatTySubst $ beta |-> fam_ty
    addFlatEvSubst $
      -- TODO ask should be refl?
      coToEvSubst (c |-> FcCoRefl (elabMonoTy fam_ty)) <> tmToEvSubst (d |-> tm)
    return
      [ GivenClsCt (FcTmVar d :| applyClsCtx ctx (TyVar beta))
      , GivenEqCt (FcCoVar c :| fam_ty :~: TyVar beta)
      ]
canonicalizeGiven _ = empty

newtype FamCtx = FamCtx { applyFamCtx :: RnMonoTy -> RnMonoTy }
newtype TyCtx  = TyCtx  { applyTyCtx  :: RnMonoTy -> RnMonoTy }
newtype ClsCtx = ClsCtx { applyClsCtx :: RnMonoTy -> RnClsCt  }

nestedFamFam :: RnMonoTy -> Maybe (FamCtx, RnMonoTy)
nestedFamFam =
  \case
    (TyFam f tys) -> first FamCtx <$> ctxList (TyFam f) tys
    _ -> Nothing

nestedFamTy :: RnMonoTy -> Maybe (TyCtx, RnMonoTy)
nestedFamTy ty = first TyCtx <$> ctxTy id ty

nestedFamCls :: RnClsCt -> Maybe (ClsCtx, RnMonoTy)
nestedFamCls (ClsCt cls tys) = first ClsCtx <$> ctxList (ClsCt cls) tys

ctxTy :: (RnMonoTy -> t) -> RnMonoTy -> Maybe (RnMonoTy -> t, RnMonoTy)
ctxTy func =
  \case
    TyApp ty1 ty2 ->
      ctxTy (func . flip TyApp ty2) ty1 <|> ctxTy (func . TyApp ty1) ty2
    TyFam f tys
      | all isOrphan tys -> Just (func, TyFam f tys)
      | otherwise -> ctxList (func . TyFam f) tys
    _ -> Nothing

ctxList :: ([RnMonoTy] -> t) -> [RnMonoTy] -> Maybe (RnMonoTy -> t, RnMonoTy)
ctxList func (ty:tys) =
  ctxTy (\ty' -> func $ ty' : tys) ty <|>
  ctxList (\tys' -> func $ ty : tys') tys
ctxList _ [] = Nothing

-- TODO split up rules to defer DINSTW
-- TODO split up local and instance schemes
topreactWanted :: Theory -> WantedCt -> MaybeT EntailM WantedCs
topreactWanted theory (WantedClsCt (d :| ClsCt cls tys)) = do
  untchs <- getUntchs
  fmap WantedClsCt <$> go untchs (theory_schemes theory)
  where
    go _ [] = empty
    go untchs ((d' :| CtrScheme bs cls_cs (ClsCt cls' tys')):schemes)
      | cls == cls'
      , Right ty_subst <- unify untchs (zipWithExact (:~:) tys tys') = do
        (ds, ann_cls_cs) <- annotateClsCs $ substInClsCs ty_subst cls_cs
        -- TODO freshen existentials
        let fc_subbed_bs = map elabMonoTy . substInTyVars ty_subst $ labelOf bs
        let ev_subst =
              d |->
               foldl
                 FcTmApp
                 (foldl FcTmTyApp (FcTmVar d') fc_subbed_bs)
                 (FcTmVar <$> ds)
        addSolvTmSubst ev_subst
        return ann_cls_cs
      | otherwise = go untchs schemes
topreactWanted theory (WantedEqCt (c :| TyFam f tys :~: ty)) = do
  untchs <- getUntchs
  fmap WantedEqCt <$> go untchs (theory_axioms theory)
  where
    go _ [] = empty
    go untchs (Axiom g as f' tys' ty':axioms)
      | f == f'
      , Right ty_subst <- unify untchs (zipWithExact (:~:) tys tys') = do
        c' <- freshFcCoVar
        let sub_as = elabMonoTy . substInMonoTy ty_subst . TyVar <$> as
        addSolvCoSubst $ c |-> FcCoTrans (FcCoAx g sub_as) (FcCoVar c')
        return [c' :| substInMonoTy ty_subst ty' :~: ty]
      | otherwise = go untchs axioms
topreactWanted _ _ = empty

topreactGiven :: Theory -> GivenCt -> MaybeT EntailM GivenCs
topreactGiven theory (GivenEqCt (co :| TyFam f tys :~: ty)) = do
  untchs <- getUntchs
  fmap GivenEqCt <$> go untchs (theory_axioms theory)
  where
    go _ [] = empty
    go untchs (Axiom g as f' tys' ty':axioms)
      | f == f'
      , Right ty_subst <- unify untchs (zipWithExact (:~:) tys tys') = do
        let sub_as = elabMonoTy . substInMonoTy ty_subst . TyVar <$> as
        let sub_ty' = substInMonoTy ty_subst ty'
        return [FcCoTrans (FcCoSym (FcCoAx g sub_as)) co :| sub_ty' :~: ty]
      | otherwise = go untchs axioms

-- We don't need a class case here
topreactGiven _ _ = empty

exhaust :: (Alternative m, Monad m) => (a -> m [a]) -> [a] -> m [a]
exhaust f xs = do
  (output, rest) <- tryRule f xs
  let new_xs = output <> rest
  exhaust f new_xs <|> pure new_xs

tryRule :: Alternative f => (a -> f b) -> [a] -> f (b, [a])
tryRule _f []     =  empty
tryRule f (x:xs)  =  flip (,) xs  <$>         f x
                 <|> second (x :) <$> tryRule f xs

exhaustSquared :: (Monad m, Alternative m) => (a -> a -> m [a]) -> [a] -> m [a]
exhaustSquared f xs = do
  (output, rest) <- tryRuleSquared f xs
  let new_xs = output <> rest
  exhaustSquared f new_xs <|> pure new_xs

-- order matters in interaction rules, hence the `flip`
tryRuleSquared :: Alternative f => (a -> a -> f b) -> [a] -> f (b, [a])
tryRuleSquared _ []      = empty
tryRuleSquared f (x:xs)  =  tryRule ( f  x) xs
                        <|> tryRule (`f` x) xs
                        <|> second (x :) <$> tryRuleSquared f xs

exhaustProduct ::
     (Monad m, Alternative m) => (g -> w -> m [w]) -> [g] -> [w] -> m [w]
exhaustProduct f xs ys = do
  (output_ys, rest_ys) <- tryRuleProduct f xs ys
  let new_ys = output_ys <> rest_ys
  exhaustProduct f xs new_ys <|> pure new_ys

-- we don't consume givens with `simplify`
tryRuleProduct :: Alternative f => (g -> w -> f o) -> [g] -> [w] -> f (o, [w])
tryRuleProduct _ []     _   = empty
tryRuleProduct f (x:xs) ys  =  tryRule (f x) ys
                           <|> tryRuleProduct f xs ys
