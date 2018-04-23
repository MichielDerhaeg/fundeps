{-# LANGUAGE FlexibleContexts #-}

module Frontend.TcUnify
  ( unify
  , doesNotOccurIn
  ) where

import           Frontend.HsTypes

import           Utils.Alternative
import           Utils.Errors
import           Utils.PrettyPrint  hiding (empty, (<>))
import           Utils.Substitution
import           Utils.Var

import           Control.Monad.Except
import           Data.Monoid

-- * Type Unification
-- ------------------------------------------------------------------------------

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError CompileError m => [RnTyVar] -> EqCs -> m HsTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- tryRule one_step eqs
  = do subst2 <- unify untchs (substInEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = tcFail $ vcat [ text "Unification failed."
                              , text "Residual constraints" <+> colon <+> ppr eqs
                              , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: EqCt -> Maybe (HsTySubst, EqCs)
    one_step (TyVar v1 :~: TyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step (TyVar v :~: ty)
      | v `notElem` untchs, v `doesNotOccurIn` ty = Just (v |-> ty, [])
    one_step (ty :~: TyVar v)
      | v `notElem` untchs, v `doesNotOccurIn` ty = Just (v |-> ty, [])
    one_step (_ :~: TyVar _) = Nothing
    one_step (TyVar _ :~: _) = Nothing
    one_step (TyCon tc1 :~: TyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
      | otherwise  = Nothing
    one_step (TyApp ty1 ty2 :~: TyApp ty3 ty4)
      = Just (mempty, [ty1 :~: ty3, ty2 :~: ty4])
    one_step (TyCon {} :~: TyApp {}) = Nothing
    one_step (TyApp {} :~: TyCon {}) = Nothing
    one_step (TyFam {} :~: _) = Nothing
    one_step (_ :~: TyFam {}) = Nothing

-- | Occurs check.
--   Returns `True` if the given variable does not occur in the given type.
doesNotOccurIn :: RnTyVar -> RnMonoTy -> Bool
doesNotOccurIn _ TyCon {}        = True
doesNotOccurIn a (TyApp ty1 ty2) = a `doesNotOccurIn` ty1 && a `doesNotOccurIn` ty2
doesNotOccurIn a (TyVar b)       = a /= b
doesNotOccurIn a (TyFam _ tys)   = (a `doesNotOccurIn`) `all` tys
