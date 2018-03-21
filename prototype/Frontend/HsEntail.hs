module Frontend.HsEntail where

import           Backend.FcTypes
import           Frontend.HsTypeChecker
import           Frontend.HsTypes

import           Utils.Annotated
import           Utils.FreeVars
import           Utils.Substitution
import           Utils.Var

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

-- | Substitute an equality within a type and generate a coercion.
-- This is weird, type type signature could be more precise.
-- Instead of returning what we passed and throwing it away.
coTy :: GivenEqCt -> RnMonoTy -> GivenEqCt
coTy ct@(_co :| (TyVar a :~: _ty)) (TyVar b)
  | a == b = ct
  | otherwise = FcCoRefl (elabMonoTy (TyVar b)) :| (TyVar b :~: TyVar b)
coTy ct@(_co :| (TyVar a :~: ty)) (TyApp ty1 ty2) =
  (FcCoApp co1' co2') :| ((TyApp ty1 ty2) :~: (substVar a ty (TyApp ty1 ty2)))
  where
    co1' :| _ = coTy ct ty1
    co2' :| _ = coTy ct ty2
coTy (_co :| (TyVar _a :~: _ty)) tc@(TyCon _tc) =
  FcCoRefl (elabMonoTy tc) :| (tc :~: tc)
coTy ct@(_co :| (TyVar a :~: ty)) tyfam@(TyFam f tys) =
  (FcCoFam (rnTyFamToFcFam f) crcs) :| (tyfam :~: substVar a ty tyfam)
  where
    crcs = labelOf (coTy ct <$> tys)
coTy _ _ = error "TODO"

-- TODO getting type class dict tycon is monadic and Fc only
-- just rewrap the name or reuse the unique?
coCt :: GivenEqCt -> RnClsCt -> GivenEqCt
coCt ct@(_co :| (TyVar a :~: ty)) (ClsCt cls tys) =
  (fcCoApp (FcCoRefl (FcTyCon undefined)) crcs) :| ((dict_ty) :~: (substVar a ty dict_ty))
    where
      dict_ty = foldl TyApp (TyCon undefined) tys
      crcs = labelOf (coTy ct <$> tys)
coCt _ _ = error "TODO"

fcCoApp :: FcCoercion -> [FcCoercion] -> FcCoercion -- TODO move to FcTypes
fcCoApp co crcs = foldl FcCoApp co crcs

isCan :: TypeCt -> Bool
isCan (EqualityCt (TyVar a :~: ty)) =
  isOrphan ty && not (a `elem` ftyvsOf ty) && ((TyVar a) `smallerThan` ty)
isCan (EqualityCt (TyFam _f tys :~: ty)) = all isOrphan (ty:tys)
isCan (ClassCt (ClsCt _cls tys)) = all isOrphan tys
isCan _ct = False

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

interactWanted :: WantedCt -> WantedCt -> TcM (WantedCs, EvSubst)
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
  , let (co :| (_ty1 :~: sub_ty2)) = coTy (FcCoVar c1 :| ct1) ty2 = do
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [c1 :| ct1, c2' :| (TyVar b :~: sub_ty2)]
      , coToEvSubst (c2 |-> FcCoTrans (FcCoVar c2') (FcCoSym co)))
interactWanted (WantedEqCt (c1 :| ct1@(TyVar     a :~: _ty1)))
               (WantedEqCt (c2 :|     (TyFam f tys :~:  ty2)))
  -- EQFEQ
  | isCan (EqualityCt ct1), a `elem` ftyvsOf (ty2 : tys)
  , let (co1 :| (_ :~: sub_tyfam)) = coTy (FcCoVar c1 :| ct1) (TyFam f tys)
  , let (co2 :| (_ :~: sub_ty2  )) = coTy (FcCoVar c1 :| ct1) ty2 = do
    c2' <- freshFcCoVar
    return
      ( WantedEqCt <$> [ c1 :| ct1, c2' :| (sub_tyfam :~: sub_ty2)]
      , coToEvSubst (c2 |-> FcCoTrans co1 (FcCoTrans (FcCoVar c2') (FcCoSym co2))))
interactWanted (WantedEqCt  (c :| ct1@(TyVar a :~: _ty)))
               (WantedClsCt (d :| ct2@(ClsCt cls   tys)))
  -- EQDICT
  | isCan (EqualityCt ct1), a `elem` ftyvsOf tys
  , let (co :| (_ :~: sub_cls)) = coCt (FcCoVar c :| ct1) ct2
  , let sub_tys = undefined sub_cls = do -- TODO
    d' <- freshDictVar
    return
      ( [WantedEqCt (c :| ct1), WantedClsCt (d' :| (ClsCt cls sub_tys))]
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
  | tys1 `undefined` tys2, cls1 == cls2 = do -- TODO type equality
    return
      ( [WantedClsCt (d1 :| ClsCt cls1 tys1)]
      , tmToEvSubst (d2 |-> FcTmVar d1))
interactWanted _ _ = error "TODO"
