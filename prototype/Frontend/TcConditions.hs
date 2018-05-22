{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}

module Frontend.TcConditions where

import           Frontend.FunDep
import           Frontend.HsTypes
import           Frontend.TcEntail
import           Frontend.TcMonad

import           Utils.Annotated
import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var

import           Control.Monad (forM_, unless, when)
import           Data.Foldable (asum)
import           Data.List     (nub, (\\))
import           Data.Semigroup

-- | The size norm
class SizeOf a where
  sizeOf :: a -> Int

instance SizeOf (MonoTy a) where
  sizeOf TyCon {}        = 1
  sizeOf (TyApp ty1 ty2) = sizeOf ty1 + sizeOf ty2
  sizeOf TyVar {}        = 1
  -- Should not occur, only with user-defined type families
  sizeOf TyFam {}        = error "Conditions: type family found"

instance SizeOf (ClsCt a) where
  sizeOf (ClsCt _ tys) = sum $ sizeOf <$> tys

instance SizeOf CtrScheme where
  sizeOf (CtrScheme _as cs ct) = sum (sizeOf <$> cs) + sizeOf ct

-- | Free variable occurrences
class OccOf a t | t -> a where
  occOf :: a -> t -> Int

instance Eq a => OccOf (HsTyVar a) (MonoTy a) where
  occOf _ TyCon {}        = 0
  occOf a (TyApp ty1 ty2) = occOf a ty1 + occOf a ty2
  occOf a (TyVar b)       = if a == b then 1 else 0
  occOf a (TyFam _ tys)   = sum $ occOf a <$> tys

instance Eq a => OccOf (HsTyVar a) (ClsCt a) where
  occOf a (ClsCt _cls tys) = sum $ occOf a <$> tys

instance OccOf (HsTyVar Name) CtrScheme where
  occOf a (CtrScheme as cs ct)
    | a `elem` labelOf as = error "Conditions: shadowing (occOf)"
    | otherwise = occOf a ct + sum (occOf a <$> cs)

-- | Fixed set of variables of a monotype
fixed :: RnMonoTy -> [RnTyVar]
fixed (TyVar a)       = [a]
fixed (TyApp ty1 ty2) = fixed ty1 <> fixed ty2
fixed TyCon {}        = mempty
fixed TyFam {}        = mempty

-- * Termination of Type Inference
-- ------------------------------------------------------------------------------

-- | Checks if the superclass relation of a class forms an acyclic graph
cycleCheck :: RnClass -> TcM ()
cycleCheck = go []
  where
    go checked cls = do
      when (cls `elem` checked) $
        throwErrorM $
        ppr cls <+>
        colon <+>
        text "The superclass relation of the class does not form an acyclic graph"
      super_cs <- fmap cls_ct_to_cls <$> lookupClsSuper cls
      mapM_ (go (cls : checked)) super_cs
    cls_ct_to_cls (ClsCt cls _) = cls

-- | Termination check for a class instance
termCheckInstance :: CtrScheme -> TcM ()
termCheckInstance scheme@(CtrScheme as cs ins_head) =
  unless (occCheck && sizeCheck) $
  throwErrorM $
  text "The instance declaration does not satisfy the termination conditions" <>
  colon $$
  ppr scheme
  where
    occCheck = and [occOf a ct <= occOf a ins_head | a <- labelOf as, ct <- cs]
    sizeCheck = and [sizeOf ct < sizeOf ins_head | ct <- cs]

-- | Termination check of a generated axiom
-- not enforcing this one, will be replaced
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

-- * Unambiguous instance/class context check
-- ------------------------------------------------------------------------------

-- | Check if an instance/class context is ambiguous
unambiguousCheck :: [RnTyVar] -> [RnTyVar] -> RnClsCs -> TcM ()
unambiguousCheck bs as cs = do
  subst <- determinacy as cs
  unless (bs \\ substDom subst == mempty) $
    throwErrorM $ text "Ambigiuous context" <+> colon <+> vcat (punctuate comma
         [ text "bs" <+> colon <+> ppr bs
         , text "as" <+> colon <+> ppr as
         , text "class constraints" <+> colon <+> ppr cs
         ])

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: Theory -> RnClsCt -> TcM ()
overlapCheck theory cls_ct@(ClsCt cls1 tys1) =
  case asum (overlaps <$> theory_schemes theory) of
    Just msg -> throwErrorM msg
    Nothing  -> return ()
  where
    overlaps (_ :| scheme@(CtrScheme _ _ (ClsCt cls2 tys2)))
      | cls1 == cls2
      , Right {} <- unify [] (zipWithExact (:~:) tys1 tys2) =
        Just $ text "Overlapping instances" <+> colon $$ ppr cls_ct $$ ppr scheme
      | otherwise = Nothing

-- * Functional Dependency Property
-- ------------------------------------------------------------------------------

-- | Check the compatibility condition
checkCompat :: Theory -> CtrScheme -> TcM ()
checkCompat theory scheme@(CtrScheme _bs cs (ClsCt cls tys)) = do
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
              throwErrorM $
                text "Compatability condition violated for" <> colon
                $$ ppr scheme
            _ -> return ()
      | otherwise = return ()

-- | Check the unambiguous witness condition
checkUnambWitness :: CtrScheme -> TcM ()
checkUnambWitness scheme@(CtrScheme _bs cs (ClsCt cls tys)) = do
  as <- lookupClsParams cls
  fds <- lookupClsFundeps cls
  forM_ fds $ \(Fundep ais ai0) -> do
    let subst = buildSubst (zipExact as tys)
    let ui0:uis = substInMonoTy subst . TyVar <$> ai0 : ais
    det_subst <- determinacy (ftyvsOf uis) cs
    let det_subst_dom = substDom det_subst
    unless (null (ftyvsOf ui0 \\ det_subst_dom)) $
      throwErrorM $ text "Unambiguous witness condition violated for" <> colon <+> ppr scheme
    -- TODO check for equality of image
    unless (length det_subst_dom == length (nub det_subst_dom)) $
      throwErrorM $ text "Unambiguous witness condition violated for" <> colon <+> ppr scheme

-- * Ambiguous type checking
-- ------------------------------------------------------------------------------

checkUnambType :: RnPolyTy -> TcM ()
checkUnambType poly_ty = do
  let (_, cs, ty) = destructPolyTy poly_ty
  let fixed_ty_vars = fixed ty
  det_subst <- determinacy fixed_ty_vars cs
  unless (null $ ftyvsOf cs \\ substDom det_subst <> fixed_ty_vars) $
    throwErrorM $ text "Ambiguous type" <> colon <+> ppr poly_ty
