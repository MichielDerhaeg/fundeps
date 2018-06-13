{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Substitution where

import           Backend.FcTypes
import           Frontend.HsTypes

import           Utils.Annotated
import           Utils.Kind
import           Utils.PrettyPrint
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Monad     (liftM2)
import           Data.Semigroup

-- * The SubstVar Class
-- ------------------------------------------------------------------------------

class SubstVar v t x | v x -> t where -- The FD means that we can not use the class for renaming substitutions.
  substVar :: v -> t -> x -> x

instance SubstVar v t x => SubstVar v t [x] where
  substVar v t xs = map (substVar v t) xs

-- * Source Language SubstVar Instances (Type Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a type variable for a type in a type
instance SubstVar RnTyVar RnMonoTy RnMonoTy where
  substVar a ty = \case
    TyVar b
      | a == b    -> ty
      | otherwise -> TyVar b
    TyCon tc      -> TyCon tc
    TyApp ty1 ty2 -> TyApp (substVar a ty ty1) (substVar a ty ty2)
    TyFam f tys   -> TyFam f (map (substVar a ty) tys)

-- | Substitute a type variable for a type in a class constraint
instance SubstVar RnTyVar RnMonoTy RnClsCt where
  substVar a ty (ClsCt cls mono) = ClsCt cls (substVar a ty mono)

-- | Substitute a type variable for a type in a qualified type
instance SubstVar RnTyVar RnMonoTy RnQualTy where
  substVar a aty = \case
    QMono    ty -> QMono (substVar a aty ty)
    QQual ct ty -> QQual (substVar a aty ct) (substVar a aty ty)

-- | Substitute a type variable for a type in a type scheme
instance SubstVar RnTyVar RnMonoTy RnPolyTy where
  substVar a aty = \case
    PQual ty      -> PQual (substVar a aty ty)
    PPoly (b :| kind) ty
      | a == b    -> error "substTyVarInPolyTy: Shadowing"
      | otherwise -> PPoly (b :| kind) (substVar a aty ty)

instance SubstVar RnTyVar RnMonoTy EqCt where
  substVar a aty (ty1 :~: ty2) = substVar a aty ty1 :~: substVar a aty ty2

-- | Substitute a type variable for a type in a constraint scheme
instance SubstVar RnTyVar RnMonoTy CtrScheme where
  substVar a ty (CtrScheme as cs ct)
    | a `elem` fmap labelOf as = error "substTyVarInScheme: Shadowing"
    | otherwise = CtrScheme as (substVar a ty cs) (substVar a ty ct)

instance SubstVar RnTyVar RnMonoTy AnnTypeCt where
  substVar a ty (AnnClsCt ct) = AnnClsCt $ fmap (substVar a ty) ct
  substVar a ty (AnnEqCt  ct) = AnnEqCt  $ fmap (substVar a ty) ct

-- * Target Language SubstVar Instances (Type Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a type variable for a type in a type
instance SubstVar FcTyVar FcType FcType where
  substVar a ty = \case
    FcTyVar b
      | a == b      -> ty
      | otherwise   -> FcTyVar b
    FcTyAbs b ty1
      | a == b      -> error "substFcVarInFcType: Shadowing (tyabs)"
      | otherwise   -> FcTyAbs b (substVar a ty ty1)
    FcTyApp ty1 ty2 -> FcTyApp (substVar a ty ty1) (substVar a ty ty2)
    FcTyCon tc      -> FcTyCon tc
    FcTyQual phi aty -> FcTyQual (substVar a ty phi) (substVar a ty aty)
    FcTyFam f tys   -> FcTyFam f $ map (substVar a ty) tys

-- | Substitute a type variable for a type in a term
instance SubstVar FcTyVar FcType FcTerm where
  substVar a aty = \case
    FcTmVar x            -> FcTmVar x
    FcTmAbs x ty tm      -> FcTmAbs x (substVar a aty ty) (substVar a aty tm)
    FcTmApp tm1 tm2      -> FcTmApp (substVar a aty tm1) (substVar a aty tm2)
    FcTmTyAbs b tm
      | a == b           -> error "substFcTyVarInTm: Shadowing (tyabs)"
      | otherwise        -> FcTmTyAbs b (substVar a aty tm)
    FcTmTyApp tm ty      -> FcTmTyApp (substVar a aty tm) (substVar a aty ty)
    FcTmDataCon dc       -> FcTmDataCon dc
    FcTmLet x ty tm1 tm2 -> FcTmLet x (substVar a aty ty) (substVar a aty tm1) (substVar a aty tm2)
    FcTmCase tm cs       -> FcTmCase (substVar a aty tm) (map (substVar a aty) cs)
    FcTmPropAbs c phi t  -> FcTmPropAbs c (substVar a aty phi) (substVar a aty t)
    FcTmCoApp t co       -> FcTmCoApp (substVar a aty t) (substVar a aty co)
    FcTmCast t co        -> FcTmCast (substVar a aty t) (substVar a aty co)

-- | Substitute a type variable for a type in a case alternative
instance SubstVar FcTyVar FcType FcAlt where
  substVar a ty (FcAlt (FcConPat k bs cs vs) tm)
    | a `elem` bs = error "substFcTyvarInTm: Shadowing (FcAlt)"
    | otherwise =
      FcAlt
        (FcConPat
           k
           bs
           ((fmap . fmap) (substVar a ty) cs)
           ((fmap . fmap) (substVar a ty) vs))
        (substVar a ty tm)

-- | Substitute a type variable for a type in a proposition
instance SubstVar FcTyVar FcType FcProp where
  substVar a aty (FcProp ty1 ty2) = FcProp (substVar a aty ty1) (substVar a aty ty2)

-- | Substitute a type variable for a type in a coercion
instance SubstVar FcTyVar FcType FcCoercion where
  substVar a aty = \case
    FcCoVar v -> FcCoVar v
    FcCoAx ax tys -> FcCoAx ax $ map (substVar a aty) tys
    FcCoRefl ty -> FcCoRefl $ substVar a aty ty
    FcCoSym co -> FcCoSym $ substVar a aty co
    FcCoTrans co1 co2 -> FcCoTrans (substVar a aty co1) (substVar a aty co2)
    FcCoApp co1 co2 -> FcCoApp (substVar a aty co1) (substVar a aty co2)
    FcCoLeft co -> FcCoLeft $ substVar a aty co
    FcCoRight co -> FcCoRight $ substVar a aty co
    FcCoFam f crs -> FcCoFam f $ map (substVar a aty) crs
    FcCoAbs b co
      | a == b -> error "substFcTyInCo: Shadowing (FcCoAbs)"
      | otherwise -> FcCoAbs b $ substVar a aty co
    FcCoInst co1 co2 -> FcCoInst (substVar a aty co1) (substVar a aty co2)
    FcCoQual phi co -> FcCoQual (substVar a aty phi) (substVar a aty co)
    FcCoQInst co1 co2 -> FcCoQInst (substVar a aty co1) (substVar a aty co2)

-- * Target Language SubstVar Instances (Term Substitution)
-- ------------------------------------------------------------------------------

-- | Substitute a term variable for a term in a term
instance SubstVar FcTmVar FcTerm FcTerm where
  substVar x xtm = \case
    FcTmVar y
      | x == y      -> xtm
      | otherwise   -> FcTmVar y
    FcTmAbs y ty tm
      | x == y      -> error "substFcTmVarInTm: Shadowing (tmabs)"
      | otherwise   -> FcTmAbs y ty (substVar x xtm tm)
    FcTmApp tm1 tm2 -> FcTmApp (substVar x xtm tm1) (substVar x xtm tm2)

    FcTmTyAbs a tm  -> FcTmTyAbs a (substVar x xtm tm)
    FcTmTyApp tm ty -> FcTmTyApp (substVar x xtm tm) ty
    FcTmDataCon dc  -> FcTmDataCon dc
    FcTmLet y ty tm1 tm2
      | x == y      -> error "substFcTmVarInTm: Shadowing (let)"
      | otherwise   -> FcTmLet y ty (substVar x xtm tm1) (substVar x xtm tm2)
    FcTmCase tm cs  -> FcTmCase (substVar x xtm tm) (map (substVar x xtm) cs)
    FcTmPropAbs c phi t -> FcTmPropAbs c phi (substVar x xtm t)
    FcTmCoApp t co -> FcTmCoApp (substVar x xtm t) co
    FcTmCast t co -> FcTmCast (substVar x xtm t) co

-- | Substitute a term variable for a term in a case alternative
instance SubstVar FcTmVar FcTerm FcAlt where
  substVar x xtm (FcAlt p@(FcConPat _dc bs cs vs) tm)
    | not (distinct bs && distinct (labelOf cs) && distinct (labelOf vs)) =
      -- extra redundancy for safety, TODO maybe put distinct checking in the type checker
      error "substFcTmVarInAlt: Variables in pattern are not distinct"
    | any (== x) (labelOf vs) = error "substFcTmVarInAlt: Shadowing"
    | otherwise = FcAlt p (substVar x xtm tm)

-- * Target Language SubstVar Instances (Coercion Substitution)
-- ------------------------------------------------------------------------------

-- TODO implement specialised functions and types

-- | Substitute a coercion variable for a coercion in a coercion
instance SubstVar FcCoVar FcCoercion FcCoercion where
  substVar c co = \case
    FcCoVar c'
      | c == c'        -> co
      | otherwise      -> FcCoVar c'
    FcCoSym co'        -> FcCoSym $ substVar c co co'
    FcCoTrans co1 co2  -> FcCoTrans (substVar c co co1) (substVar c co co2)
    FcCoApp co1 co2    -> FcCoApp (substVar c co co1) (substVar c co co2)
    FcCoLeft co'       -> FcCoLeft $ substVar c co co'
    FcCoRight co'      -> FcCoRight $ substVar c co co'
    FcCoFam f crs      -> FcCoFam f $ map (substVar c co) crs
    FcCoAbs a co'      -> FcCoAbs a $ substVar c co co'
    FcCoInst co1 co2   -> FcCoInst (substVar c co co1) (substVar c co co2)
    FcCoQual prop co'  -> FcCoQual prop $ substVar c co co'
    FcCoQInst co1 co2  -> FcCoQInst (substVar c co co1) (substVar c co co2)
    co' -> co'

-- | Substitute a coercion variable for a coercion in a Fc term
instance SubstVar FcCoVar FcCoercion FcTerm where
  substVar c co = \case
    FcTmVar y            -> FcTmVar y
    FcTmAbs y ty tm      -> FcTmAbs y ty $ substVar c co tm
    FcTmApp tm1 tm2      -> FcTmApp (substVar c co tm1) (substVar c co tm2)
    FcTmTyAbs a tm       -> FcTmTyAbs a (substVar c co tm)
    FcTmTyApp tm ty      -> FcTmTyApp (substVar c co tm) ty
    FcTmDataCon dc       -> FcTmDataCon dc
    FcTmLet y ty tm1 tm2 -> FcTmLet y ty (substVar c co tm1) (substVar c co tm2)
    FcTmCase tm cs       -> FcTmCase (substVar c co tm) (map (substVar c co) cs)
    FcTmPropAbs c' phi t
      | c == c'          -> error "TODO"
      | otherwise        -> FcTmPropAbs c' phi (substVar c co t)
    FcTmCoApp t co'      -> FcTmCoApp (substVar c co t) (substVar c co co')
    FcTmCast t co'       -> FcTmCast (substVar c co t) (substVar c co co')

-- | Substitute a coercion variable for a coercion in a case alternative
-- TODO distinct checking?
instance SubstVar FcCoVar FcCoercion FcAlt where
  substVar c co (FcAlt (FcConPat dc bs cs vs) tm)
    | any (==c) (labelOf cs) = error "substFcCoercionInAlt: Shadowing"
    | otherwise = FcAlt (FcConPat dc bs cs vs) (substVar c co tm)

-- ------------------------------------------------------------------------------

-- | General structure of substitutions as snoc lists
data Sub x y = SNil | SCons (Sub x y) x y

mapSub :: (x -> x') -> (y -> y') -> Sub x y -> (Sub x' y')
mapSub _fx _fy SNil          = SNil
mapSub  fx  fy (SCons s x y) = SCons (mapSub fx fy s) (fx x) (fy y)

instance (PrettyPrint x, PrettyPrint y) => PrettyPrint (Sub x y) where
  ppr = brackets . sep . punctuate comma. reverse . to_doc_list
    where
      to_doc_list SNil          = []
      to_doc_list (SCons s x y) = (ppr x <+> text "|->" <+> ppr y) : to_doc_list s

  needsParens _ = False

instance Semigroup (Sub x y) where
  (<>) = mappend

instance Monoid (Sub x y) where
  mempty = SNil
  mappend sub SNil          = sub
  mappend sub (SCons s x y) = SCons (mappend sub s) x y
  mconcat = foldl mappend SNil -- foldl since mappend does induction on the second argument

instance Subst (Sub x y) x y where
  (|->) x y = SCons SNil x y

-- | GEORGE: DOCUMENT ME
sub_rec :: SubstVar v t x => Sub v t -> x -> x
sub_rec SNil          t = t
sub_rec (SCons s x y) t = sub_rec s (substVar x y t)

buildSubst :: [(x,y)] -> Sub x y
buildSubst = foldl (\s (x,y) -> SCons s x y) SNil

destructSubst :: Sub x y -> [(x,y)]
destructSubst SNil = []
destructSubst (SCons s x y) = destructSubst s <> [(x,y)]

-- | Compute the domain of the substitution
substDom :: Sub x y -> [x]
substDom SNil             = []
substDom (SCons sub x _y) = x : substDom sub

-- | Return true if the substitution is empty
nullSubst :: Sub x y -> Bool
nullSubst SNil = True
nullSubst _    = False

-- * The ApplySubst Class
-- ------------------------------------------------------------------------------

class ApplySubst s t where
  applySubst :: s -> t -> t

instance ApplySubst s t => ApplySubst s [t] where
  applySubst s xs = map (applySubst s) xs

instance SubstVar v t x => ApplySubst (Sub v t) x where
  applySubst = sub_rec

-- * Type Substitution (Source Language)
-- ------------------------------------------------------------------------------

type HsTySubst = Sub RnTyVar RnMonoTy

-- | Build a type substitution from an association list between type variables
buildRnSubst :: [(RnTyVar, RnTyVar)] -> HsTySubst
buildRnSubst = foldl (\s (x,y) -> SCons s x (TyVar y)) SNil

-- | Apply a type substitution to a monotype
substInMonoTy :: HsTySubst -> RnMonoTy -> RnMonoTy
substInMonoTy = sub_rec

-- | Apply a type substitution to a type equality
substInEqCt :: HsTySubst -> EqCt -> EqCt
substInEqCt subst (ty1 :~: ty2) = substInMonoTy subst ty1 :~: substInMonoTy subst ty2

-- | Apply a type substitution to a a list of type equalities
substInEqCs :: HsTySubst -> EqCs -> EqCs
substInEqCs subst = map (substInEqCt subst)

-- | Apply a type substitution to a a list of annotated type equalities
substInAnnEqCs :: HsTySubst -> AnnEqCs -> AnnEqCs
substInAnnEqCs subst = (fmap . fmap) (substInEqCt subst)

-- | Apply a type substitution to a class constraint
substInClsCt :: HsTySubst -> RnClsCt -> RnClsCt
substInClsCt = sub_rec

-- | Apply a type substitution to a list of class constraints
substInClsCs :: HsTySubst -> RnClsCs -> RnClsCs
substInClsCs subst = map (substInClsCt subst)

-- | Apply a type substitution to a list of annotated class constraints
substInAnnClsCs :: HsTySubst -> AnnClsCs -> AnnClsCs
substInAnnClsCs subst = (fmap . fmap) (substInClsCt subst)

-- | Apply a type substitution to a type variable
substInTyVar :: HsTySubst -> RnTyVar -> RnMonoTy
substInTyVar subst tv = substInMonoTy subst (TyVar tv)

-- | Apply a type substitution to a list of type variables
substInTyVars :: HsTySubst -> [RnTyVar] -> [RnMonoTy]
substInTyVars subst = map (substInTyVar subst)

-- | Apply a type substitution to a program theory
substInProgramTheory :: HsTySubst -> ProgramTheory -> ProgramTheory
substInProgramTheory subst = (fmap . fmap) (substInScheme subst)

-- | Apply a type substitution to a constraint scheme
substInScheme :: HsTySubst -> CtrScheme -> CtrScheme
substInScheme = sub_rec

-- | Apply a type substitution to a qualified type
substInQualTy :: HsTySubst -> RnQualTy -> RnQualTy
substInQualTy = sub_rec

-- | Apply a type substitution to a type scheme
substInPolyTy :: HsTySubst -> RnPolyTy -> RnPolyTy
substInPolyTy = sub_rec

-- | Apply a type substitution to a annotated type contraint
substInAnnTypeCt :: HsTySubst -> AnnTypeCt -> AnnTypeCt
substInAnnTypeCt = sub_rec

-- | Apply a type substitution to annotated type contraints
substInAnnTypeCs :: HsTySubst -> AnnTypeCs -> AnnTypeCs
substInAnnTypeCs subst = fmap (substInAnnTypeCt subst)

-- * System F Type Substitution
-- ------------------------------------------------------------------------------

type FcTySubst = Sub FcTyVar FcType

-- | Apply a type substitution to a type
substFcTyInTy :: FcTySubst -> FcType -> FcType
substFcTyInTy = sub_rec

-- | Apply a type substitution to a term
substFcTyInTm :: FcTySubst -> FcTerm -> FcTerm
substFcTyInTm = sub_rec

-- | Apply a type substitution to a case alternative
substFcTyInAlt :: FcTySubst -> FcAlt -> FcAlt
substFcTyInAlt = sub_rec -- XXX: subst (FcAlt p tm) = FcAlt p (substFcTyInTm subst tm)
  -- GEORGE: Now the patterns do not bind type variables so we don't have to check for shadowing here.

substFcTyInCo :: FcTySubst -> FcCoercion -> FcCoercion
substFcTyInCo = sub_rec

-- * System F Term Substitution
-- ------------------------------------------------------------------------------

type FcTmSubst = Sub FcTmVar FcTerm

-- | Apply a term substitution to a term
substFcTmInTm :: FcTmSubst -> FcTerm -> FcTerm
substFcTmInTm = sub_rec

-- | Apply a term substitution to a case alternative
substFcTmInAlt :: FcTmSubst -> FcAlt -> FcAlt
substFcTmInAlt = sub_rec

-- * System Fc Proposition Substitution
-- ------------------------------------------------------------------------------

substFcTyInProp :: FcTySubst -> FcProp -> FcProp
substFcTyInProp = sub_rec

-- * System Fc Coercion Substitution
-- ------------------------------------------------------------------------------

type FcCoSubst = Sub FcCoVar FcCoercion

-- | Apply a coercion substitution to a coercion
substFcCoInCo :: FcCoSubst -> FcCoercion -> FcCoercion
substFcCoInCo = sub_rec

-- | Apply a coercion substitution to a term
substFcCoInTm :: FcCoSubst -> FcTerm -> FcTerm
substFcCoInTm = sub_rec


-- * Evidence Substitution
-- ------------------------------------------------------------------------------

data EvSubst = EvSubst FcTmSubst FcCoSubst

instance ApplySubst EvSubst FcTerm where
  applySubst (EvSubst tm_subst co_subst) =
    applySubst co_subst . applySubst tm_subst

instance ApplySubst EvSubst FcCoercion where
  applySubst (EvSubst _tm_subst co_subst) =
    applySubst co_subst

instance Semigroup EvSubst where
  (<>) = mappend

instance Monoid EvSubst where
  mempty = EvSubst mempty mempty
  mappend (EvSubst tm1 co1) (EvSubst tm2 co2) =
    EvSubst (mappend tm1 tm2) (mappend co1 co2)
  mconcat = foldl mappend mempty -- TODO correct?

-- | Apply a evidence substitution to a term
substEvInTm :: EvSubst -> FcTerm -> FcTerm
substEvInTm = applySubst

-- | Apply a evidence substitution to a coercion
substEvInCo :: EvSubst -> FcCoercion -> FcCoercion
substEvInCo = applySubst

-- | Convert a coercion substitution to a evidence substitution
coToEvSubst :: FcCoSubst -> EvSubst
coToEvSubst co_subst = EvSubst mempty co_subst

-- | Convert a term substitution to a evidence substitution
tmToEvSubst :: FcTmSubst -> EvSubst
tmToEvSubst tm_subst = EvSubst tm_subst mempty

-- | Apply a type substitution to image of an evidence substitution
substTyInEvidence :: FcTySubst -> EvSubst -> EvSubst
substTyInEvidence subst (EvSubst tm_subst co_subst) =
  EvSubst sub_tm_subst sub_co_subst
  where
    sub_tm_subst = mapSub id (substFcTyInTm subst) tm_subst
    sub_co_subst = mapSub id (substFcTyInCo subst) co_subst

-- | Apply evidence substitution to image of another evidence substitution
substEvInEvidence :: EvSubst -> EvSubst -> EvSubst
substEvInEvidence subst (EvSubst tm_subst co_subst) =
  EvSubst sub_tm_subst sub_co_subst
  where
    sub_tm_subst = mapSub id (substEvInTm subst) tm_subst
    sub_co_subst = mapSub id (substEvInCo subst) co_subst

-- | Pretty print an evidence substitution
-- TODO more pretty
instance PrettyPrint EvSubst where
  ppr (EvSubst tm_subst co_subst) = ppr tm_subst $$ ppr co_subst
  needsParens _ = False

-- * The Subst class
-- ------------------------------------------------------------------------------

class Monoid s => Subst s dom img | s -> dom img, dom img -> s where
  (|->)   :: dom -> img -> s

-- * Alpha-equality on System F Types
-- ------------------------------------------------------------------------------

-- | Alpha equality on types
alphaEqFcTypes :: MonadUnique m => FcType -> FcType -> m Bool
alphaEqFcTypes (FcTyVar a)       (FcTyVar b)       = return (a == b)
alphaEqFcTypes (FcTyAbs a ty1) (FcTyAbs b ty2) = do
  -- GEORGE: Do we need to check that the kinds are the same?
  -- Need to go over the implementation at some point soon.
  c <- FcTyVar <$> freshFcTyVar (kindOf a)
  let ty1' = substFcTyInTy (a |-> c) ty1
  let ty2' = substFcTyInTy (b |-> c) ty2
  alphaEqFcTypes ty1' ty2'
alphaEqFcTypes (FcTyApp ty1 ty2) (FcTyApp ty3 ty4) = liftM2 (&&) (alphaEqFcTypes ty1 ty3) (alphaEqFcTypes ty2 ty4)
alphaEqFcTypes (FcTyCon tc1)     (FcTyCon tc2)     = return (tc1 == tc2)
alphaEqFcTypes (FcTyQual (FcProp ty1 ty2) ty3) (FcTyQual (FcProp ty4 ty5) ty6) =
  and <$> mapM (uncurry alphaEqFcTypes) [(ty1, ty4), (ty2, ty5), (ty3, ty6)]
alphaEqFcTypes (FcTyFam f1 tys1) (FcTyFam f2 tys2) =
  and . ((f1 == f2) :) <$> mapM (uncurry alphaEqFcTypes) (zip tys1 tys2)

alphaEqFcTypes (FcTyVar  {}) _ = return False
alphaEqFcTypes (FcTyAbs  {}) _ = return False
alphaEqFcTypes (FcTyApp  {}) _ = return False
alphaEqFcTypes (FcTyCon  {}) _ = return False
alphaEqFcTypes (FcTyFam  {}) _ = return False
alphaEqFcTypes (FcTyQual {}) _ = return False

-- * Freshen up all local binders
-- ------------------------------------------------------------------------------

class FreshenLclBndrs a where
  freshenLclBndrs :: MonadUnique m => a -> m a

-- | Freshen the (type) binders of a type scheme
instance FreshenLclBndrs RnPolyTy where
  freshenLclBndrs (PQual ty) = return (PQual ty)
  freshenLclBndrs (PPoly (a :| _) ty) = freshRnTyVar (kindOf a) >>= \b ->
    PPoly (b :| kindOf b) <$> freshenLclBndrs (substVar a (TyVar b) ty)

-- | Freshen the (type) binders of a System F type
instance FreshenLclBndrs FcType where
  freshenLclBndrs (FcTyVar a)       = return (FcTyVar a)
  freshenLclBndrs (FcTyAbs a ty)    = freshFcTyVar (kindOf a) >>= \b ->
    FcTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) ty)
  freshenLclBndrs (FcTyApp ty1 ty2) = FcTyApp <$> freshenLclBndrs ty1 <*> freshenLclBndrs ty2
  freshenLclBndrs (FcTyCon tc)      = return (FcTyCon tc)
  freshenLclBndrs (FcTyFam f tys)   = FcTyFam f <$> mapM freshenLclBndrs tys
  freshenLclBndrs (FcTyQual phi t) =
    FcTyQual <$> freshenLclBndrs phi <*> freshenLclBndrs t

-- | Freshen the (type + term) binders of a System F term
instance FreshenLclBndrs FcTerm where
  freshenLclBndrs (FcTmAbs x ty tm) = freshFcTmVar >>= \y ->
    FcTmAbs y <$> freshenLclBndrs ty <*> freshenLclBndrs (substVar x (FcTmVar y) tm)
  freshenLclBndrs (FcTmVar x)       = return (FcTmVar x)
  freshenLclBndrs (FcTmApp tm1 tm2) = FcTmApp <$> freshenLclBndrs tm1 <*> freshenLclBndrs tm2
  freshenLclBndrs (FcTmTyAbs a tm)  = freshFcTyVar (kindOf a) >>= \b ->
    FcTmTyAbs b <$> freshenLclBndrs (substVar a (FcTyVar b) tm)
  freshenLclBndrs (FcTmTyApp tm ty) = FcTmTyApp <$> freshenLclBndrs tm <*> freshenLclBndrs ty
  freshenLclBndrs (FcTmDataCon dc)  = return (FcTmDataCon dc)
  freshenLclBndrs (FcTmLet x ty tm1 tm2) = freshFcTmVar >>= \y ->
    FcTmLet y <$> freshenLclBndrs ty
              <*> freshenLclBndrs (substVar x (FcTmVar y) tm1)
              <*> freshenLclBndrs (substVar x (FcTmVar y) tm2)

  freshenLclBndrs (FcTmCase tm cs) = FcTmCase <$> freshenLclBndrs tm <*> mapM freshenLclBndrs cs
  freshenLclBndrs (FcTmPropAbs c phi t) = do
    c' <- freshFcCoVar
    FcTmPropAbs c' <$> freshenLclBndrs phi <*>
      freshenLclBndrs (substVar c (FcCoVar c') t)
  freshenLclBndrs (FcTmCoApp t co) = FcTmCoApp <$> freshenLclBndrs t <*> freshenLclBndrs co
  freshenLclBndrs (FcTmCast t co) = FcTmCast <$> freshenLclBndrs t <*> freshenLclBndrs co

-- | Freshen the (type + term) binders of a System F case alternative
instance FreshenLclBndrs FcAlt where
  freshenLclBndrs (FcAlt (FcConPat dc bs cs vs) tm) = do
    bs' <- mapM (freshFcTyVar . kindOf) bs
    cs' <- mapM (const freshFcCoVar) (labelOf cs)
    vs' <- mapM (const freshFcTmVar) (labelOf vs)
    let ty_subst = buildSubst . zip bs $ map FcTyVar bs'
    let co_subst = buildSubst . zip (labelOf cs) $ map FcCoVar cs'
    let tm_subst = buildSubst . zip (labelOf vs) $ map FcTmVar vs'
    FcAlt (FcConPat dc bs' (cs' |: dropLabel cs) (vs' |: dropLabel vs)) <$>
      freshenLclBndrs
        (applySubst ty_subst (applySubst co_subst (applySubst tm_subst tm)))

-- | Freshen the binders of a constraint scheme
instance FreshenLclBndrs CtrScheme where
  freshenLclBndrs (CtrScheme as cs ct) = do
    new_as <- mapM (freshRnTyVar . kindOf) (labelOf as)
    let local_subst = buildRnSubst $ zip (labelOf as) new_as
    return $
      CtrScheme
        (new_as |: fmap kindOf new_as)
        (substInClsCs local_subst cs)
        (substInClsCt local_subst ct)

-- | Freshen the binders of the types in a propotition
instance FreshenLclBndrs FcProp where
  freshenLclBndrs (FcProp ty1 ty2) =
    FcProp <$> freshenLclBndrs ty1 <*> freshenLclBndrs ty2

-- | Freshen the binders of a coercion
instance FreshenLclBndrs FcCoercion where
  freshenLclBndrs (FcCoVar c) = return $ FcCoVar c
  freshenLclBndrs (FcCoAx g tys) = FcCoAx g <$> mapM freshenLclBndrs tys
  freshenLclBndrs (FcCoRefl ty) = FcCoRefl <$> freshenLclBndrs ty
  freshenLclBndrs (FcCoSym co) = FcCoSym <$> freshenLclBndrs co
  freshenLclBndrs (FcCoTrans co1 co2) =
    FcCoTrans <$> freshenLclBndrs co1 <*> freshenLclBndrs co2
  freshenLclBndrs (FcCoApp co1 co2) =
    FcCoApp <$> freshenLclBndrs co1 <*> freshenLclBndrs co2
  freshenLclBndrs (FcCoLeft co) = FcCoLeft <$> freshenLclBndrs co
  freshenLclBndrs (FcCoRight co) = FcCoRight <$> freshenLclBndrs co
  freshenLclBndrs (FcCoFam f crcs) = FcCoFam f <$> mapM freshenLclBndrs crcs
  freshenLclBndrs (FcCoAbs a co) = do
    a' <- freshFcTyVar (kindOf a)
    FcCoAbs a' <$> freshenLclBndrs (substVar a (FcTyVar a') co)
  freshenLclBndrs (FcCoInst co1 co2) =
    FcCoInst <$> freshenLclBndrs co1 <*> freshenLclBndrs co2
  freshenLclBndrs (FcCoQual phi co) =
    FcCoQual <$> freshenLclBndrs phi <*> freshenLclBndrs co
  freshenLclBndrs (FcCoQInst co1 co2) =
    FcCoQInst <$> freshenLclBndrs co1 <*> freshenLclBndrs co2
