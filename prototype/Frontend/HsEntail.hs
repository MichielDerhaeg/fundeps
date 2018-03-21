module Frontend.HsEntail where

import Frontend.HsTypes
import Frontend.HsTypeChecker
import Backend.FcTypes

import Utils.Annotated
import Utils.Var
import Utils.Substitution

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
