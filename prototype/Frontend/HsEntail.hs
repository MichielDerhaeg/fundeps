{-# LANGUAGE LambdaCase     #-}

module Frontend.HsEntail where

import           Backend.FcTypes
import           Frontend.HsTypeChecker
import           Frontend.HsTypes

import           Utils.Annotated
import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var

import           Control.Applicative
import           Control.Arrow       (first, (***))
import           Control.Monad.State

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

type FlatSubst = HsTySubst

data EntailState = EntailState
  { untouchables  :: [RnTyVar]
  , flat_ty_subst :: FlatSubst
  , flat_ev_subst :: EvSubst
  , solv_ev_subst :: EvSubst
  }

getUntchs :: EntailM [RnTyVar]
getUntchs = gets untouchables

addUntch :: RnTyVar -> EntailM ()
addUntch a = modify $ \s -> s { untouchables = a : untouchables s }

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

-- TODO getting type class dict tycon is monadic and Fc only
-- just rewrap the name or reuse the unique?
coCt :: FcCoercion -> RnTyVar -> RnMonoTy -> RnClsCt -> (FcCoercion, RnClsCt)
coCt co a ty ct@(ClsCt cls tys) =
  (fcCoApp (FcCoRefl (FcTyCon cls_tc)) crcs, substVar a ty ct)
    where
      cls_tc = undefined cls
      crcs =  fst . coTy co a ty <$> tys

fcCoApp :: FcCoercion -> [FcCoercion] -> FcCoercion -- TODO move to FcTypes
fcCoApp = foldl FcCoApp

isCan :: TypeCt -> Bool
isCan (EqualityCt ct) = isCanEq  ct
isCan (ClassCt ct)    = isCanCls ct

isCanEq :: EqCt -> Bool
isCanEq (TyVar a :~: ty) =
  isOrphan ty && a `notElem` ftyvsOf ty && (TyVar a `smallerThan` ty)
isCanEq (TyFam _f tys :~: ty) = all isOrphan (ty:tys)
isCanEq _ = False

isCanCls :: RnClsCt -> Bool
isCanCls (ClsCt _cls tys) = all isOrphan tys

smallerThan :: RnMonoTy -> RnMonoTy -> Bool
smallerThan (TyVar a) (TyVar b) = isUniVar a || a <= b
smallerThan TyVar {} ty = isOrphan ty
smallerThan TyFam {} TyVar {} = True
smallerThan TyFam {} TyApp {} = True
smallerThan TyFam {} TyCon {} = True
smallerThan _ _ = False

-- | Checks if the type contains no type families
isOrphan :: RnMonoTy -> Bool
isOrphan TyCon {} = True
isOrphan (TyApp ty1 ty2) = isOrphan ty1 && isOrphan ty2
isOrphan TyVar {} = True
isOrphan TyFam {} = False

interactWanted :: WantedCt -> WantedCt -> EntailM (WantedCs, EvSubst)
interactWanted (WantedEqCt (c1 :| ct1@(TyVar a :~: ty1)))
               (WantedEqCt (c2 :| ct2@(TyVar b :~: ty2)))
  -- EQSAME
  | a == b, isCan (EqualityCt ct1), isCan (EqualityCt ct2) = do
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| (ty1 :~: ty2)]
      , coToEvSubst (c2 |-> FcCoTrans (FcCoVar c1) (FcCoVar c2')))
  -- EQDIFF
  | a `elem` ftyvsOf ty2, isCan (EqualityCt ct1), isCan (EqualityCt ct2)
  , let (co, sub_ty2) = coTy (FcCoVar c1) a ty1 ty2 = do
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| (TyVar b :~: sub_ty2)]
      , coToEvSubst (c2 |-> FcCoTrans (FcCoVar c2') (FcCoSym co)))
interactWanted (WantedEqCt (c1 :| ct1@(TyVar     a :~:  ty1)))
               (WantedEqCt (c2 :|     (TyFam f tys :~:  ty2)))
  -- EQFEQ
  | isCan (EqualityCt ct1), a `elem` ftyvsOf (ty2 : tys)
  , let (co1, sub_tyfam) = coTy (FcCoVar c1) a ty1 (TyFam f tys)
  , let (co2, sub_ty2)   = coTy (FcCoVar c1) a ty1 ty2 = do
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [ c1 :| ct1, c2' :| (sub_tyfam :~: sub_ty2)]
      , coToEvSubst (c2 |-> FcCoTrans co1 (FcCoTrans (FcCoVar c2') (FcCoSym co2))))
interactWanted (WantedEqCt  (c :| ct1@(TyVar a :~: ty)))
               (WantedClsCt (d :| ct2@(ClsCt _cls tys)))
  -- EQDICT
  | isCan (EqualityCt ct1), a `elem` ftyvsOf tys
  , let (co, sub_cls) = coCt (FcCoVar c) a ty ct2 = do
    d' <- freshDictVar
    return
      ( [WantedEqCt (c :| ct1), WantedClsCt (d' :| sub_cls)]
      , tmToEvSubst (d |-> FcTmCast (FcTmVar d') (FcCoSym co)))
interactWanted (WantedEqCt (c1 :| ct1@(TyFam _f1 _tys1 :~: ty1)))
               (WantedEqCt (c2 :|     (TyFam _f2 _tys2 :~: ty2))) = do
  -- FEQFEQ
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| (ty1 :~: ty2)]
      , coToEvSubst (c2 |-> FcCoTrans (FcCoVar c1) (FcCoVar c2')))
interactWanted (WantedClsCt (d1 :| ClsCt cls1 tys1))
               (WantedClsCt (d2 :| ClsCt cls2 tys2))
  -- DDICT
  | and (zipWithExact eqMonoTy tys1 tys2), cls1 == cls2 =
    return
      ( [WantedClsCt (d1 :| ClsCt cls1 tys1)]
      , tmToEvSubst (d2 |-> FcTmVar d1))
interactWanted _ _ = error "TODO"

-- TODO always return first total constraint? order important?
interactGiven :: GivenCt -> GivenCt -> EntailM GivenCs
interactGiven (GivenEqCt (co1 :| ct1@(TyVar a :~: ty1)))
              (GivenEqCt (co2 :| ct2@(TyVar b :~: ty2)))
  -- EQSAME
  | a == b, isCan (EqualityCt ct1), isCan (EqualityCt ct2) =
  return
    ( GivenEqCt <$> [co1 :| ct1
    , FcCoTrans (FcCoSym co1) co2 :| (ty1 :~: ty2)])
  -- EQDIFF
  | a `elem` ftyvsOf ty2, isCan (EqualityCt ct1), isCan (EqualityCt ct2)
  , let (co, sub_ty) = coTy co1 a ty1 ty2 =
  return
    ( GivenEqCt <$> [co1 :| ct1
    , FcCoTrans co2 co :| (TyVar b :~: sub_ty)])
interactGiven (GivenEqCt (co1 :|  ct1@(TyVar a       :~: ty1)))
              (GivenEqCt (co2 :| (fam@(TyFam _f tys) :~: ty2)))
  -- EQFEQ
  | isCan (EqualityCt ct1), a `elem` ftyvsOf tys
  , let (co1', sub_fam) = coTy co1 a ty1 fam
  , let (co2', sub_ty2) = coTy co1 a ty1 ty2 =
  return ( GivenEqCt <$> [co1 :| ct1
         , FcCoTrans (FcCoSym co1') (FcCoTrans co2 co2') :| (sub_fam :~: sub_ty2)])
interactGiven (GivenEqCt  (co :| ct1@(TyVar a :~: ty)))
              (GivenClsCt (tm :| ct2@(ClsCt _cls tys)))
  -- EQDICT
  | isCan (EqualityCt ct1), a `elem` ftyvsOf tys
  , let (co', sub_cls) = coCt co a ty ct2 =
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
interactGiven _ _ = error "TODO"

-- TODO WantedCs or Maybe WantedCt because never more than 1 result
simplify :: GivenCt -> WantedCt -> EntailM (WantedCs, EvSubst)
simplify (GivenEqCt  (co :| ct1@(TyVar a :~: ty1)))
         (WantedEqCt (c  :| ct2@(TyVar b :~: ty2)))
  -- SEQSAME
  | a == b, isCan (EqualityCt ct1), isCan (EqualityCt ct2) = do
  c' <- freshFcCoVar
  return ( [ WantedEqCt (c' :| (ty1 :~: ty2))]
         , coToEvSubst (c |-> FcCoTrans co (FcCoVar c')))
  -- SEQDIFF
  | a `elem` ftyvsOf ty2, isCan (EqualityCt ct1), isCan (EqualityCt ct2)
  , let (co', sub_ty2) = coTy co a ty1 ty2 = do
  c' <- freshFcCoVar
  return ( [WantedEqCt (c' :| (TyVar b :~: sub_ty2))]
         , coToEvSubst (c |-> FcCoTrans (FcCoVar c') (FcCoSym co')))
simplify (GivenEqCt  (co :| ct1@(TyVar a            :~: ty1)))
         (WantedEqCt (c  :|     (fam@(TyFam _f tys) :~: ty2)))
  -- SEQFEQ
  | a `elem` ftyvsOf tys, isCanEq ct1
  , let (co', sub_fam) = coTy co a ty1 fam = do
  c' <- freshFcCoVar
  return ( [ WantedEqCt (c' :| (sub_fam :~: ty2))]
         , coToEvSubst ( c |-> FcCoTrans co' (FcCoVar c')))
simplify (GivenEqCt   (co :| ct1@(TyVar a :~: ty1)))
         (WantedClsCt (d  :| ct2@(ClsCt _cls  tys)))
  -- SEQDICT
  | a `elem` ftyvsOf tys, isCanEq ct1
  , let (co', sub_cls) = coCt co a ty1 ct2 = do
  d' <- freshDictVar
  return ( [ WantedClsCt (d' :| sub_cls)]
         , tmToEvSubst (d |-> FcTmCast (FcTmVar d') (FcCoSym co')))
simplify (GivenEqCt   (co :| (fam1@TyFam {} :~: ty1)))
         (WantedEqCt  (c  :| (fam2@TyFam {} :~: ty2)))
  -- SFEQFEQ
  | eqMonoTy fam1 fam2 = do
  c' <- freshFcCoVar
  return ( [WantedEqCt (c' :| (ty1 :~: ty2))]
         , coToEvSubst (c |-> FcCoTrans co (FcCoVar c')))
simplify (GivenClsCt  (tm :| ClsCt cls1 tys1))
         (WantedClsCt (d  :| ClsCt cls2 tys2))
  | cls1 == cls2, and (zipWithExact eqMonoTy tys1 tys2) =
  return (mempty, tmToEvSubst (d |-> tm))
simplify _ _ = error "TODO"

canonicalizeWanted :: WantedCt -> EntailM (WantedCs, EvSubst)
canonicalizeWanted (WantedEqCt (c :| ct)) =
  (fmap WantedEqCt *** coToEvSubst) <$> go ct
  where
    go :: EqCt -> EntailM (AnnEqCs, FcCoSubst)
    -- REFLW
    go (ty1 :~: ty2)
      | eqMonoTy ty1 ty2 = return (mempty, c |-> FcCoRefl (elabMonoTy ty1))
    -- TYAPPW
    go (TyApp ty1 ty2 :~: TyApp ty3 ty4) = do
      [c1, c2] <- genFreshCoVars 2
      return
        ( [c1 :| (ty1 :~: ty3), c2 :| (ty2 :~: ty4)]
        , c |-> FcCoApp (FcCoVar c1) (FcCoVar c2))
    -- FAILDECW
    go (TyCon tc1 :~: TyCon tc2)
      | tc1 /= tc2 = throwErrorM $ text "TODO"
    -- OCCCHECKW
    go (TyVar a :~: ty)
      | a `elem` ftyvsOf ty
      , not (eqMonoTy (TyVar a) ty) = throwErrorM $ text "TODO occurscheck"
    -- ORIENTW
    go (ty1 :~: ty2)
      | ty2 `smallerThan` ty1 = do
        c' <- freshFcCoVar
        return ([c' :| (ty2 :~: ty1)], c |-> FcCoSym (FcCoVar c'))
    -- FFLATWL
    go (search_ty :~: ty)
      | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamFam search_ty = do
        [c1, c2] <- genFreshCoVars 2
        beta     <- lift $ lookupTyFamKind f >>= freshRnTyVar
        let ctx_beta = applyFamCtx ctx (TyVar beta)
        let (co, _ty) =
              coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        return
          ( [c1 :| (fam_ty :~: TyVar beta), c2 :| (ctx_beta :~: ty)]
          , c |-> FcCoTrans (FcCoSym co) (FcCoVar c2))
    -- FFLATWR
    go (ty :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f1 _)) <- nestedFamTy search_ty
      , TyFam {} <- ty = do
        [c1, c2] <- genFreshCoVars 2
        beta <- lift $ lookupTyFamKind f1 >>= freshRnTyVar
        let ctx_beta = applyTyCtx ctx (TyVar beta)
        let (co, _) = coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        return
          ( [c1 :| (fam_ty :~: TyVar beta), c2 :| (ty :~: ctx_beta)]
          , c |-> FcCoTrans (FcCoVar c2) co)
    -- TODO merge with above somehow
    go (ty@TyVar {} :~: search_ty)
      | Just (ctx, fam_ty@(TyFam f1 _)) <- nestedFamTy search_ty = do
        [c1, c2] <- genFreshCoVars 2
        beta <- lift $ lookupTyFamKind f1 >>= freshRnTyVar
        let ctx_beta = applyTyCtx ctx (TyVar beta)
        let (co, _) = coTy (FcCoSym (FcCoVar c1)) beta fam_ty ctx_beta
        return
          ( [c1 :| (fam_ty :~: TyVar beta), c2 :| (ty :~: ctx_beta)]
          , c |-> FcCoTrans (FcCoVar c2) co)
    go _ = error "TODO"
canonicalizeWanted (WantedClsCt (d :| cls_ct))
  -- DFLATW
  | Just (ctx, fam_ty@(TyFam f _tys)) <- nestedFamCls cls_ct = do
    c' <- freshFcCoVar
    d' <- freshDictVar
    beta <- lift $ lookupTyFamKind f >>= freshRnTyVar
    let ctx_beta    = applyClsCtx ctx (TyVar beta)
    let (co, _ty) = coCt (FcCoSym (FcCoVar c')) beta fam_ty ctx_beta
    return
      ( [ WantedEqCt  (c' :| (fam_ty :~: TyVar beta))
        , WantedClsCt (d' :| ctx_beta)
        ]
      , tmToEvSubst (d |-> FcTmCast (FcTmVar d') co))
canonicalizeWanted _ = error "TODO"

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

-- TODO cleanup
unifyM :: EqCs -> EntailM (Maybe HsTySubst)
unifyM eq_cs = do
  untchs <- getUntchs
  return $
    case unify untchs eq_cs of
      Right ty_subst -> Just ty_subst
      Left {}        -> Nothing

canonicalizeGiven :: GivenCt -> EntailM GivenCs
canonicalizeGiven _ = error "TODO"

topreactWanted :: WantedCt -> EntailM (WantedCs, EvSubst)
topreactWanted _ = error "TODO"

topreactGiven :: GivenCt -> EntailM GivenCs
topreactGiven _ = error "TODO"
