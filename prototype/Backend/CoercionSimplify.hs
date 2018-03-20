module Backend.CoercionSimplify
  ( simplifyFcProgram
  ) where

import           Backend.FcTypes
import           Utils.Annotated
import           Utils.Utils

import           Control.Applicative

-- | Repeatedly simplify a System Fc program until no rules apply.
-- Returns `Nothing` if it can't be simplified anymore.
simplifyFcProgram :: FcProgram -> Maybe FcProgram
simplifyFcProgram = keep go
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

simplifyFcTerm :: FcTerm -> Maybe FcTerm
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
    go (FcTmPropAbs c prop tm) = doAlt2 (FcTmPropAbs c)
      simplifyProp prop
      go tm
    go (FcTmCoApp tm co) = doAlt2 FcTmCoApp
      go tm
      simplifyCoercion co
    go (FcTmCast tm co) = doAlt2 FcTmCast
      go tm
      simplifyCoercion co

simplifyFcType :: FcType -> Maybe FcType
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

simplifyFcAlts :: FcAlts -> Maybe FcAlts
simplifyFcAlts alts = doAltList simplifyFcAlt alts

simplifyFcAlt :: FcAlt -> Maybe FcAlt
simplifyFcAlt (FcAlt (FcConPat dc bs ann_cs ann_xs) tm) = doAlt3 pat
  (doAltList simplifyProp)   (dropLabel ann_cs)
  (doAltList simplifyFcType) (dropLabel ann_xs)
  simplifyFcTerm tm
  where
    pat props tys tm' = FcAlt (FcConPat dc bs (labelOf ann_cs |: props) (labelOf ann_xs |: tys)) tm'

simplifyProp :: FcProp -> Maybe FcProp
simplifyProp (FcProp ty1 ty2) = doAlt2 FcProp
  simplifyFcType ty1
  simplifyFcType ty2

simplifyCoercion :: FcCoercion -> Maybe FcCoercion
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

doAlt2 :: Alternative f => (a -> b -> c) -> (a -> f a) -> a -> (b -> f b) -> b -> f c
doAlt2 pat f1 x1 f2 x2 =  pat <$>   f1 x1 <*> pure x2
                      <|> pat <$> pure x1 <*>   f2 x2

doAlt3 ::
     Alternative f
  => (a -> b -> c -> d)
  -> (a -> f a)
  -> a
  -> (b -> f b)
  -> b
  -> (c -> f c)
  -> c
  -> f d
doAlt3 pat f1 x1 f2 x2 f3 x3 =  pat <$>   f1 x1 <*> pure x2 <*> pure x3
                            <|> pat <$> pure x1 <*>   f2 x2 <*> pure x3
                            <|> pat <$> pure x1 <*> pure x2 <*>   f3 x3

doAltList :: Alternative f => (a -> f a) -> [a] -> f ([a])
doAltList _f []     = empty
doAltList  f (x:xs) = doAlt2 (:) f x (doAltList f) xs

keep :: (a -> Maybe a) -> a -> Maybe a
keep f x = case f x of
  Nothing -> Nothing
  Just x' -> case keep f x' of
    Nothing  -> Just x'
    result   -> result

