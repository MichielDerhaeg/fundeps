{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}

module Frontend.Conditions where

import           Frontend.HsConstraintGen
import           Frontend.HsEntail
import           Frontend.HsTcMonad
import           Frontend.HsTypes

import           Utils.Annotated
import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint  hiding ((<>))
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var

import           Control.Monad (forM_, unless, when)
import           Data.List     ((\\))
import           Data.Monoid


-- | The size norm
class SizeOf a where
  sizeOf :: a -> Int

instance SizeOf (MonoTy a) where
  sizeOf (TyCon {})      = 1
  sizeOf (TyApp ty1 ty2) = sizeOf ty1 + sizeOf ty2
  sizeOf (TyVar {})      = 1
  sizeOf (TyFam {})   = error "TODO"

instance SizeOf (ClsCt a) where
  sizeOf (ClsCt _ tys) = sum $ sizeOf <$> tys

instance SizeOf CtrScheme where
  sizeOf (CtrScheme _as cs ct) = sum (sizeOf <$> cs) + sizeOf ct

-- | Free variable occurrences
class OccOf a t | t -> a where
  occOf :: a -> t -> Int

instance Eq a => OccOf (HsTyVar a) (MonoTy a) where
  occOf _ (TyCon {})      = 0
  occOf a (TyApp ty1 ty2) = occOf a ty1 + occOf a ty2
  occOf a (TyVar b)       = if a == b then 1 else 0
  occOf a (TyFam _ tys)  = sum $ occOf a <$> tys

instance Eq a => OccOf (HsTyVar a) (ClsCt a) where
  occOf a (ClsCt _cls tys) = sum $ occOf a <$> tys

instance OccOf (HsTyVar Name) CtrScheme where
  occOf a (CtrScheme as cs ct)
    | a `elem` (labelOf as) = error "TODO"
    | otherwise = occOf a ct + sum (occOf a <$> cs)

-- * Termination of Type Inference
-- ------------------------------------------------------------------------------

-- | TODO check superclass relation forms acyclic graph
cycleCheck :: RnClass -> TcM ()
cycleCheck = go []
  where
    go checked cls = do
      when (cls `elem` checked) $ throwErrorM $ text "TODO"
      super_cs <- (fmap cls_ct_to_cls) <$> lookupClsSuper cls
      mapM_ (go (cls:checked)) super_cs
    cls_ct_to_cls (ClsCt cls _) = cls

-- TODO sizeCheck: sum of all cs?
termCheckInstance :: CtrScheme -> Bool
termCheckInstance (CtrScheme as cs ins_head) = occCheck && sizeCheck
  where
    occCheck = and [occOf a ct <= occOf a ins_head | a <- labelOf as, ct <- cs]
    sizeCheck = and [sizeOf ct < sizeOf ins_head | ct <- cs]

termCheckAxiom :: Axiom -> Bool
termCheckAxiom (Axiom _g as _f tys ty) = all go (findTyFams ty)
  where
    go tys' =
      null (concatMap findTyFams tys') &&
      sum (sizeOf <$> tys') < sum (sizeOf <$> tys) &&
      and [sum (occOf a <$> tys') <= sum (occOf a <$> tys) | a <- as]
    findTyFams (TyApp ty1 ty2) = findTyFams ty1 <> findTyFams ty2
    findTyFams TyVar {} = mempty
    findTyFams (TyFam _f tys') = [tys']
    findTyFams TyCon {} = mempty

terminationCheck :: CtrScheme -> Axioms -> TcM ()
terminationCheck scheme@(CtrScheme _as _cs (ClsCt cls _tys)) axioms = do
  unless (termCheckInstance scheme) $ throwErrorM $ text "TODO"
  -- maybe better to put in `generateAxioms`
  unless (termCheckAxiom `all` axioms) $ throwErrorM $ text "TODO"
  cycleCheck cls

-- * Functional Dependency Property
-- ------------------------------------------------------------------------------

-- | Check the compatibility condition
checkCompat :: Theory -> CtrScheme -> TcM ()
checkCompat theory (CtrScheme _bs cs (ClsCt cls tys)) = do
  let other_schemes = dropLabel $ theory_schemes theory
  mapM_ go other_schemes
  where
    go (CtrScheme _bs' cs' (ClsCt cls' tys'))
      | cls == cls' = do
        as <- lookupClsParams cls
        fds <- lookupClsFundeps cls
        forM_ fds $ \(Fundep ais ai0) -> do
          let subst = buildSubst (zipExact as tys)
          let subst' = buildSubst (zipExact as tys')
          let ui0:uis = substInMonoTy subst . TyVar <$> ai0 : ais
          let ui0':uis' = substInMonoTy subst' . TyVar <$> ai0 : ais
          substi <- determinacy (ftyvsOf uis) cs
          substi' <- determinacy (ftyvsOf uis') cs'
          -- compat relation
          case unify mempty (zipWithExact (:~:) uis uis') of
            Right ty_subst ->
              unless
                (substInMonoTy ty_subst (substInMonoTy substi ui0) `eqMonoTy`
                 substInMonoTy ty_subst (substInMonoTy substi' ui0')) $
              throwErrorM $ text "TODO"
            _ -> return () -- dunno
      | otherwise = return ()

-- | Check the unambiguous witness condition
-- TODO how to check subst(ui0) independent on order
checkUnambWitness :: CtrScheme -> TcM ()
checkUnambWitness (CtrScheme _bs cs (ClsCt cls tys)) = do
  as <- lookupClsParams cls
  fds <- lookupClsFundeps cls
  forM_ fds $ \(Fundep ais ai0) -> do
    let subst = buildSubst (zipExact as tys)
    let ui0:uis = substInMonoTy subst . TyVar <$> ai0 : ais
    det_subst <- determinacy (ftyvsOf uis) cs
    unless (null (ftyvsOf ui0 \\ substDom det_subst)) $
      throwErrorM $ text "TODO"
