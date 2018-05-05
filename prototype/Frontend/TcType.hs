{-# LANGUAGE LambdaCase #-}

module Frontend.TcType where

import           Frontend.HsTypes
import           Frontend.TcMonad

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.Ctx
import           Utils.Errors
import           Utils.Kind
import           Utils.PrettyPrint
import           Utils.Substitution
import           Utils.Var

import           Control.Monad (unless)

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
