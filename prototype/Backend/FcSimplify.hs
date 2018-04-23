{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Backend.FcSimplify
  ( fcSimplify
  ) where

import           Backend.FcTypes

import           Utils.Alternative
import           Utils.Annotated
import           Utils.AssocList
import           Utils.Ctx
import           Utils.Substitution
import           Utils.Utils

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.State


fcSimplify :: FcProgram -> FcProgram
fcSimplify pgm = case simplifyFcProgram pgm of
  Nothing -> pgm
  Just pgm' -> pgm'

-- | Repeatedly simplify a System Fc program until no rules apply.
-- Returns `Nothing` if it can't be simplified anymore.
simplifyFcProgram :: FcProgram -> Maybe FcProgram
simplifyFcProgram pgm = flip evalStateT (SimplEnv mempty)
                      $ flip runReaderT mempty
                      $ do buildSimplEnv pgm
                           keep go pgm
  where
    go (FcPgmTerm tm)            = FcPgmTerm           <$> simplifyFcTerm tm
    go (FcPgmDataDecl  decl pgm) = FcPgmDataDecl  decl <$> go pgm
    go (FcPgmAxiomDecl decl pgm) = FcPgmAxiomDecl decl <$> go pgm
    go (FcPgmFamDecl   decl pgm) = FcPgmFamDecl   decl <$> go pgm
    go (FcPgmValDecl (FcValBind f ty tm) pgm) = doAlt2 pat
      simplifyFcTerm tm
      go pgm
      where
        pat tm' pgm' = FcPgmValDecl (FcValBind f ty tm') pgm'

simplifyFcTerm :: FcTerm -> SimplifyM FcTerm
simplifyFcTerm = go
  where
    -- rewrite rules
    go (FcTmCast tm (FcCoRefl _co)) = pure tm

    -- normal traversal
    go (FcTmAbs a ty tm) = doAlt2 (FcTmAbs a)
      simplifyFcType ty
      go tm
    go (FcTmVar _a) = empty
    go (FcTmApp tm1 tm2) = doAlt2 FcTmApp
      go tm1
      go tm2
    go (FcTmTyAbs t tm) = FcTmTyAbs t <$> go tm
    go (FcTmTyApp tm ty) = doAlt2 FcTmTyApp
      go tm
      simplifyFcType ty
    go (FcTmDataCon _dc) = empty
    go (FcTmLet a ty tm_let tm_in) = doAlt3 (FcTmLet a)
      simplifyFcType ty
      go tm_let
      go tm_in
    go (FcTmCase tm alts) = doAlt2 FcTmCase
      go tm
      simplifyFcAlts alts
    go (FcTmPropAbs c prop tm) = extendCtxM c prop $ doAlt2 (FcTmPropAbs c)
      simplifyProp prop
      go tm
    go (FcTmCoApp tm co) = doAlt2 FcTmCoApp
      go tm
      simplifyCoercion co
    go (FcTmCast tm co) = doAlt2 FcTmCast
      go tm
      simplifyCoercion co

simplifyFcType :: FcType -> SimplifyM FcType
simplifyFcType = go
  where
    go (FcTyVar _a) = empty
    go (FcTyAbs a ty) = FcTyAbs a <$> go ty
    go (FcTyApp ty1 ty2) = doAlt2 FcTyApp
      go ty1
      go ty2
    go (FcTyCon _tc) = empty
    go (FcTyQual prop ty) = doAlt2 FcTyQual
      simplifyProp prop
      go ty
    go (FcTyFam f tys) = FcTyFam f <$> doAltList go tys

simplifyFcAlts :: FcAlts -> SimplifyM FcAlts
simplifyFcAlts alts = doAltList simplifyFcAlt alts

simplifyFcAlt :: FcAlt -> SimplifyM FcAlt
simplifyFcAlt (FcAlt (FcConPat dc bs ann_cs ann_xs) tm) =
  extendCtxM (labelOf ann_cs) (dropLabel ann_cs) $
  doAlt3 pat
    (doAltList simplifyProp) (dropLabel ann_cs)
    (doAltList simplifyFcType) (dropLabel ann_xs)
    simplifyFcTerm tm
  where
    pat props tys tm' =
      FcAlt (FcConPat dc bs (labelOf ann_cs |: props) (labelOf ann_xs |: tys)) tm'

simplifyProp :: FcProp -> SimplifyM FcProp
simplifyProp (FcProp ty1 ty2) = doAlt2 FcProp
  simplifyFcType ty1
  simplifyFcType ty2

simplifyCoercion :: FcCoercion -> SimplifyM FcCoercion
simplifyCoercion = go
  where
    -- rewrite rules
    go (FcCoTrans (FcCoRefl _ty) co) = pure co
    go (FcCoTrans co (FcCoRefl _ty)) = pure co
    go (FcCoApp (FcCoRefl ty1) (FcCoRefl ty2)) = pure $ FcCoRefl (FcTyApp ty1 ty2)
    go (FcCoSym (FcCoSym co)) = pure co
    go (FcCoSym (FcCoRefl ty)) = pure $ FcCoRefl ty
    go (FcCoTrans (FcCoSym co1) (FcCoSym co2)) = pure $ FcCoSym (FcCoTrans co1 co2)
    go (FcCoTrans (FcCoFam f1 cos1) (FcCoFam f2 cos2))
      | f1 == f2 = pure . FcCoFam f1 $ zipWithExact FcCoTrans cos1 cos2

    -- normal traversal
    go (FcCoVar _c) = empty
    go (FcCoAx g tys) = FcCoAx g <$> doAltList simplifyFcType tys
    go (FcCoRefl ty) = FcCoRefl <$> simplifyFcType ty
    go (FcCoSym co) = FcCoSym <$> go co
    go (FcCoTrans co1 co2) = doAlt2 FcCoTrans
      go co1
      go co2
    go (FcCoApp co1 co2) = doAlt2 FcCoApp
      go co1
      go co2
    go (FcCoLeft co) = FcCoLeft <$> go co
    go (FcCoRight co) = FcCoLeft <$> go co
    go (FcCoFam f crcs) = FcCoFam f <$> doAltList go crcs
    go (FcCoAbs a co) = FcCoAbs a <$> go co
    go (FcCoInst co1 co2) = doAlt2 FcCoInst
      go co1
      go co2
    go (FcCoQual prop co) = doAlt2 FcCoQual
      simplifyProp prop
      go co
    go (FcCoQInst co1 co2) = doAlt2 FcCoQInst
      go co1
      go co2

newtype SimplEnv = SimplEnv { unSimplEnv :: AssocList FcAxVar FcAxiomInfo }

type SimplifyM = (ReaderT FcCoCtx (StateT SimplEnv Maybe))

buildSimplEnv :: FcProgram -> SimplifyM ()
buildSimplEnv (FcPgmTerm _tm)         = return ()
buildSimplEnv (FcPgmFamDecl _tm pgm)  = buildSimplEnv pgm
buildSimplEnv (FcPgmValDecl _tm pgm)  = buildSimplEnv pgm
buildSimplEnv (FcPgmDataDecl _tm pgm) = buildSimplEnv pgm
buildSimplEnv (FcPgmAxiomDecl (FcAxiomDecl g as f tys ty) pgm) = do
  modify (\(SimplEnv l) -> SimplEnv (extendAssocList g info l))
  buildSimplEnv pgm
  where
    info = FcAxiomInfo g as f tys ty

typeOfCo :: FcCoercion -> SimplifyM FcProp
typeOfCo (FcCoVar c) = lookupCoVar c
typeOfCo (FcCoAx g tys) = do
  axiom <- lookupAxiom g
  return $
    substFcTyInProp (buildSubst (zip (fc_ax_uv axiom) tys)) (axiomToProp axiom)
typeOfCo (FcCoRefl ty) = return $ FcProp ty ty
typeOfCo (FcCoSym co) = do
  FcProp ty1 ty2 <- typeOfCo co
  return $ FcProp ty2 ty1
typeOfCo (FcCoTrans co1 co2) = do
  FcProp ty1 _ <- typeOfCo co1
  FcProp _ ty2 <- typeOfCo co2
  return $ FcProp ty1 ty2
typeOfCo (FcCoApp co1 co2) = do
  FcProp ty1 ty2 <- typeOfCo co1
  FcProp ty3 ty4 <- typeOfCo co2
  return $ FcProp (FcTyApp ty1 ty3) (FcTyApp ty2 ty4)
typeOfCo (FcCoLeft co) = typeOfCo co >>= \case
  FcProp (FcTyApp ty1 _ty2) (FcTyApp ty3 _ty4) -> return $ FcProp ty1 ty3
  _ -> empty
typeOfCo (FcCoRight co) = typeOfCo co >>= \case
  FcProp (FcTyApp _ty1 ty2) (FcTyApp _ty3 ty4) -> return $ FcProp ty2 ty4
  _ -> empty
typeOfCo (FcCoFam f crcs) = do
  (tys1, tys2) <- unzip . (fmap propToTuple) <$> mapM typeOfCo crcs
  return $ FcProp (FcTyFam f tys1) (FcTyFam f tys2)
  where
    propToTuple (FcProp ty1 ty2) = (ty1, ty2)
typeOfCo (FcCoAbs a co) = do
  FcProp ty1 ty2 <- typeOfCo co
  return $ FcProp (FcTyAbs a ty1) (FcTyAbs a ty2)
typeOfCo (FcCoInst co1 co2) = typeOfCo co1 >>= \case
  FcProp (FcTyAbs a ty1) (FcTyAbs b ty2) -> do
    FcProp ty3 ty4 <- typeOfCo co2
    return $ FcProp (substVar a ty3 ty1) (substVar b ty4 ty2)
  _ -> empty
typeOfCo (FcCoQual psi co) = do
  FcProp ty1 ty2 <- typeOfCo co
  return $ FcProp (FcTyQual psi ty1) (FcTyQual psi ty2)
typeOfCo (FcCoQInst co1 _co2) = typeOfCo co1 >>= \case
  FcProp (FcTyQual _psi1 ty1) (FcTyQual _psi2 ty2) -> do
    return $ FcProp ty1 ty2
  _ -> empty

lookupAxiom :: FcAxVar -> SimplifyM FcAxiomInfo
lookupAxiom g = gets unSimplEnv >>= \l -> case lookupInAssocList g l of
  Nothing -> empty
  Just info -> pure info

lookupCoVar :: FcCoVar -> SimplifyM FcProp
lookupCoVar c = ask >>= \ctx -> case lookupCtx ctx c of
  Nothing -> empty
  Just prop -> pure prop
