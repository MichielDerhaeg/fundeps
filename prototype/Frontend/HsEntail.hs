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

type GivenEqCt = Ann FcCoercion EqCt

type GivenClsCt = Ann FcTerm RnClsCt

data GivenCt
  = GivenEqCt GivenEqCt
  | GivenClsCt GivenClsCt

-- | Substitute an equality within a type and generate a coercion.
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
