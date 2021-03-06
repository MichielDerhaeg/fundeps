{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Frontend.HsTypes where

import           Backend.FcTypes

import           Utils.Annotated
import           Utils.FreeVars
import           Utils.Kind
import           Utils.PrettyPrint
--import           Utils.SnocList
import           Utils.Unique
import           Utils.Utils
import           Utils.Var

import           Control.Arrow  (first, second)
import           Data.List      (nub, (\\))
import           Data.Semigroup

-- * Type Constructors
-- ------------------------------------------------------------------------------

newtype HsTyCon a = HsTC { unHsTC :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (HsTyCon a) where
  getUnique = getUnique . unHsTC

instance Symable a => Symable (HsTyCon a) where
  symOf = symOf . unHsTC

instance Named a => Named (HsTyCon a) where
  nameOf = nameOf . unHsTC

type PsTyCon = HsTyCon Sym
type RnTyCon = HsTyCon Name

data HsTyConInfo
  = HsTCInfo { hs_tc_ty_con    :: RnTyCon     -- ^ The type constructor name
             , hs_tc_type_args :: [RnTyVar]   -- ^ Universal types
             , hs_tc_fc_ty_con :: FcTyCon     -- ^ Elaborated Type Constructor
             , hs_tc_projs     :: [RnTyFam]   -- ^ Projection functions
             }

-- * Data Constructors
-- ------------------------------------------------------------------------------

newtype HsDataCon a = HsDC { unHsDC :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (HsDataCon a) where
  getUnique = getUnique . unHsDC

instance Symable a => Symable (HsDataCon a) where
  symOf = symOf . unHsDC

instance Named a => Named (HsDataCon a) where
  nameOf = nameOf . unHsDC

type PsDataCon = HsDataCon Sym
type RnDataCon = HsDataCon Name

data HsDataConInfo
  = HsDCInfo { hs_dc_data_con    :: RnDataCon    -- ^ The data constructor name
             , hs_dc_univ        :: [RnTyVar]    -- ^ Universal type variables
             , hs_dc_parent      :: RnTyCon      -- ^ Parent type constructor
             , hs_dc_arg_tys     :: [RnMonoTy]   -- ^ Argument types
             , hs_dc_fc_data_con :: FcDataCon }  -- ^ Elaborated Data Constructor

-- * Class Names
-- ------------------------------------------------------------------------------

newtype Class a = Class { unClass :: a }
  deriving (Eq, Ord)

instance Uniquable a => Uniquable (Class a) where
  getUnique = getUnique . unClass

instance Symable a => Symable (Class a) where
  symOf = symOf . unClass

instance Named a => Named (Class a) where
  nameOf = nameOf . unClass

type PsClass = Class Sym
type RnClass = Class Name

data Fundep a = Fundep [HsTyVar a] (HsTyVar a)

type PsFundep = Fundep Sym
type RnFundep = Fundep Name

data ClassInfo
  = ClassInfo { cls_exis      :: [RnTyVar]  -- ^ Existential type variables
              , cls_super     :: RnClsCs    -- ^ The superclass constraints
              , cls_class     :: RnClass    -- ^ The class name
              , cls_type_args :: [RnTyVar]  -- ^ Type arguments
              , cls_fundeps   :: [RnFundep] -- ^ Functional dependencies
              , cls_fd_fams   :: [RnTyFam]  -- ^ Functional dependency type families
              , cls_method    :: RnTmVar    -- ^ Method name
              , cls_method_ty :: RnPolyTy   -- ^ Method type
              , cls_tycon     :: FcTyCon    -- ^ Elaborated Type Constructor
              , cls_datacon   :: FcDataCon  -- ^ Elaborated Data Constructor
              }

data RnClsInfo
  = RnClsInfo { rn_cls_class     :: RnClass   -- ^ The class name
              , rn_cls_method    :: RnTmVar   -- ^ Method name
              }

-- * Terms
-- ------------------------------------------------------------------------------

data Term a = TmVar (HsTmVar a)                   -- ^ Term variable
            | TmCon (HsDataCon a)                 -- ^ Data constructor
            | TmAbs (HsTmVar a) (Term a)          -- ^ Lambda x . Term
            | TmApp (Term a) (Term a)             -- ^ Term application
            | TmLet (HsTmVar a) (Term a) (Term a) -- ^ Letrec var = term in term
            | TmCase (Term a) [HsAlt a]           -- ^ case e of { ... }

-- | Parsed/renamed term
type PsTerm = Term Sym
type RnTerm = Term Name

data HsAlt a = HsAlt (HsPat a) (Term a)

type PsAlt = HsAlt Sym
type RnAlt = HsAlt Name

data HsPat a = HsPat (HsDataCon a) [HsTmVar a]

type PsPat = HsPat Sym
type RnPat = HsPat Name

instance (Symable a, PrettyPrint a) => PrettyPrint (HsAlt a) where
  ppr (HsAlt pat tm) = ppr pat <+> arrow <+> ppr tm
  needsParens _      = True

instance (Symable a, PrettyPrint a) => PrettyPrint (HsPat a) where
  ppr (HsPat dc xs) = ppr dc <+> hsep (map ppr xs)
  needsParens _     = True

-- * Type Families
-- ------------------------------------------------------------------------------

-- | Type Family
newtype HsTyFam a = HsTF { unHsTF :: a }
  deriving (Eq, Ord, Uniquable, Symable, Named, PrettyPrint)

-- | Parsed/renamed type family
type PsTyFam = HsTyFam Sym
type RnTyFam = HsTyFam Name

data HsTyFamInfo = HsTFInfo
  { hs_tf_fam       :: RnTyFam   -- ^ The Type Family name
  , hs_tf_type_args :: [RnTyVar] -- ^ Universal types
  , hs_tf_kind      :: Kind      -- ^ Return kind
  }

-- * Types
-- ------------------------------------------------------------------------------

-- | Monotype
data MonoTy a = TyCon (HsTyCon a)             -- ^ Type Constructor
              | TyApp (MonoTy a) (MonoTy a)   -- ^ Type Application
              | TyVar (HsTyVar a)             -- ^ Type variable
              | TyFam (HsTyFam a) [MonoTy a] -- ^ Type Family application

-- | Parsed/renamed monotype
type PsMonoTy = MonoTy Sym
type RnMonoTy = MonoTy Name

-- | Qualified Type
data QualTy a = QMono (MonoTy a)
              | QQual (ClsCt a) (QualTy a)

-- | Parsed/renamed qualified type
type PsQualTy = QualTy Sym
type RnQualTy = QualTy Name

-- | Polytype
data PolyTy a = PQual (QualTy a)
              | PPoly (HsTyVarWithKind a) (PolyTy a)

-- | Parsed/renamed polytype
type PsPolyTy = PolyTy Sym
type RnPolyTy = PolyTy Name

arrowTyConSym :: Sym
arrowTyConSym = mkSym "(->)"

arrowTyConName :: Name
arrowTyConName = mkName arrowTyConSym arrowTyConUnique

mkPsArrowTy :: PsMonoTy -> PsMonoTy -> PsMonoTy
mkPsArrowTy ty1 ty2 = TyApp (TyApp (TyCon psArrowTyCon) ty1) ty2

psArrowTyCon :: PsTyCon
psArrowTyCon = HsTC arrowTyConSym

rnArrowTyCon :: RnTyCon
rnArrowTyCon = HsTC arrowTyConName

arrowTyConInfo :: HsTyConInfo
arrowTyConInfo = HsTCInfo rnArrowTyCon
                          [ mkRnTyVar (mkName (mkSym "a") arrowTyVar1Unique) KStar
                          , mkRnTyVar (mkName (mkSym "b") arrowTyVar2Unique) KStar ]
                          fcArrowTyCon
                          [] -- TODO

-- GEORGE: Needed for pretty printing
isArrowTyCon :: Symable a => HsTyCon a -> Bool
isArrowTyCon (HsTC a) = symOf a == arrowTyConSym

-- isArrowTyCon :: Uniquable a => HsTyCon a -> Bool
-- isArrowTyCon tc = getUnique tc == arrowTyConUnique

-- GEORGE: Needed for pretty printing
isHsArrowTy :: Symable a => MonoTy a -> Maybe (MonoTy a, MonoTy a)
isHsArrowTy (TyApp (TyApp (TyCon tc) ty1) ty2)
  | isArrowTyCon tc   = Just (ty1, ty2)
isHsArrowTy _other_ty = Nothing

-- | Checks if the type contains no type families
isTyPattern :: RnMonoTy -> Bool
isTyPattern TyCon {} = True
isTyPattern (TyApp ty1 ty2) = isTyPattern ty1 && isTyPattern ty2
isTyPattern TyVar {} = True
isTyPattern TyFam {} = False

type HsTyVarWithKind a = Ann (HsTyVar a) Kind
type PsTyVarWithKind = HsTyVarWithKind Sym
type RnTyVarWithKind = HsTyVarWithKind Name

-- * Smart constructors
-- ------------------------------------------------------------------------------

-- | Create a type constructor application
mkTyConApp :: HsTyCon a -> [MonoTy a] -> MonoTy a
mkTyConApp tc tys = foldl TyApp (TyCon tc) tys

-- | Make a renamed arrow type (uncurried)
mkRnArrowTy :: [RnMonoTy] -> RnMonoTy -> RnMonoTy
mkRnArrowTy arg_tys res_ty = foldr arr res_ty arg_tys
  where
    arr ty1 ty2 = TyApp (TyApp (TyCon rnArrowTyCon) ty1) ty2

-- * Conversions between monotypes, qualified types and polytypes
-- ------------------------------------------------------------------------------

-- | Convert (is possible) a type scheme into a monotype
polyTyToMonoTy :: PolyTy a -> Maybe (MonoTy a)
polyTyToMonoTy (PQual ty) = qualTyToMonoTy ty
polyTyToMonoTy (PPoly {}) = Nothing

-- | Convert (is possible) a qualified type into a monotype
qualTyToMonoTy :: QualTy a -> Maybe (MonoTy a)
qualTyToMonoTy (QMono ty) = Just ty
qualTyToMonoTy (QQual {}) = Nothing

-- | Lift a monotype to a qualified type
monoTyToQualTy :: MonoTy a -> QualTy a
monoTyToQualTy = QMono

-- | Lift a qualified type to a polytype
qualTyToPolyTy :: QualTy a -> PolyTy a
qualTyToPolyTy = PQual

-- | Lift a monotype to a polytype
monoTyToPolyTy :: MonoTy a -> PolyTy a
monoTyToPolyTy = PQual . QMono

-- | Take a polytype apart
destructPolyTy :: PolyTy a -> ([HsTyVarWithKind a], ClsCs a, MonoTy a) -- GEORGE: Type synonym for lists of type variables?
destructPolyTy (PQual   ty) = ([]  , cs, ty') where     (cs, ty') = destructQualTy ty
destructPolyTy (PPoly a ty) = (a:as, cs, ty') where (as, cs, ty') = destructPolyTy ty

-- | Take a qualified type apart
destructQualTy :: QualTy a -> (ClsCs a, MonoTy a)
destructQualTy (QMono    ty) = ([], ty)
destructQualTy (QQual ct ty) = (ct:cs, ty')
  where (cs, ty') = destructQualTy ty

-- | Inverse of destructPolyTy: create a polytype from parts
constructPolyTy :: ([HsTyVarWithKind a], ClsCs a, MonoTy a) -> PolyTy a
constructPolyTy (as, cs, ty) = foldr PPoly (PQual (constructQualTy (cs,ty))) as

-- | Inverse of destructQualTy: create a qualified type from parts
constructQualTy :: (ClsCs a, MonoTy a) -> QualTy a
constructQualTy (cs, ty) = foldr QQual (QMono ty) cs

-- * Syntactic Type Equality
-- ------------------------------------------------------------------------------

-- | Check if two monotypes are syntactically the same
eqMonoTy :: Eq a => MonoTy a -> MonoTy a -> Bool
eqMonoTy (TyCon tc1) (TyCon tc2) = tc1 == tc2
eqMonoTy (TyApp ty1 ty2) (TyApp ty1' ty2') =
  eqMonoTy ty1 ty1' && eqMonoTy ty2 ty2'
eqMonoTy (TyVar a) (TyVar b) = a == b
eqMonoTy (TyFam f1 tys1) (TyFam f2 tys2) =
  f1 == f2 && and (zipWithExact eqMonoTy tys1 tys2)
eqMonoTy _ _ = False

-- * Class Constraints
-- ------------------------------------------------------------------------------

-- | Class constraint(s)
data ClsCt a = ClsCt (Class a) [MonoTy a]
type ClsCs a = [ClsCt a]

-- | Parsed class constraints(s)
type PsClsCt = ClsCt Sym
type PsClsCs = ClsCs Sym

-- | Renamed class constraint(s)
type RnClsCt = ClsCt Name
type RnClsCs = ClsCs Name

-- * Programs and Declarations
-- ------------------------------------------------------------------------------

-- | Program
newtype Program a = Program {unPgm :: [Decl a]}

-- | Declaration
data Decl a = ClsDecl  (ClsDecl  a) -- ^ Class declaration
            | InsDecl  (InsDecl  a) -- ^ Instance declaration
            | DataDecl (DataDecl a) -- ^ Datatype declaration
            | ValDecl  (ValBind  a) -- ^ Value Binding

-- | Class declaration
data ClsDecl a = ClsD { cabs    :: [HsTyVarWithKind a] -- ^ Abstracted type variables
                      , csuper  :: ClsCs a             -- ^ Superclass constraints
                      , cname   :: Class a             -- ^ Class name
                      , cvars   :: [HsTyVar a]         -- ^ Type variables
                      , cfds    :: [Fundep a]          -- ^ Functional dependencies
                      , cmena   :: HsTmVar a           -- ^ Method name
                      , cmety   :: PolyTy a }          -- ^ Method type

-- | Instance declaration
data InsDecl a = InsD { iabs  :: [HsTyVarWithKind a] -- ^ Abstracted type variables
                      , icons :: ClsCs a             -- ^ Constraints
                      , iname :: Class a             -- ^ Class name
                      , ivars :: [MonoTy a]          -- ^ Instance types
                      , imena :: HsTmVar a           -- ^ Method name
                      , imetm :: Term a }            -- ^ Method term

-- | Datatype Declaration
data DataDecl a = DataD { dtycon    :: HsTyCon a                     -- ^ Type constructor
                        , dtyvars   :: [HsTyVarWithKind a]           -- ^ Universal type variables
                        , ddatacons :: [(HsDataCon a, [MonoTy a])] } -- ^ Data constructors

-- | Top-level Value Binding
data ValBind a = ValBind
  { vname :: HsTmVar a        -- ^ Value name
  , vtype :: Maybe (PolyTy a) -- ^ Optional value type
  , vbind :: Term a           -- ^ Bound term
  }

-- | Parsed/renamed programs
type PsProgram = Program Sym
type RnProgram = Program Name

-- | Parsed/renamed declarations
type PsDecl = Decl Sym
type RnDecl = Decl Name

-- | Parsed/renamed class declarations
type PsClsDecl = ClsDecl Sym
type RnClsDecl = ClsDecl Name

-- | Parsed/renamed instance declarations
type PsInsDecl = InsDecl Sym
type RnInsDecl = InsDecl Name

-- | Parsed/renamed datatype declarations
type PsDataDecl = DataDecl Sym
type RnDataDecl = DataDecl Name

-- | Parsed/renamed value bindings
type PsValBind = ValBind Sym
type RnValBind = ValBind Name

-- * Additional Syntax For Type Inference And Elaboration
-- ------------------------------------------------------------------------------

-- | Class constraint scheme
data CtrScheme = CtrScheme [RnTyVarWithKind] RnClsCs RnClsCt

-- | Equality constraint(s)
data EqCt = RnMonoTy :~: RnMonoTy
type EqCs = [EqCt]
infix 9 :~:

-- | Variable-annotated class constraints
type AnnClsCt = Ann DictVar RnClsCt
type AnnClsCs = [AnnClsCt]

-- | Variable-annotated constraint schemes
type AnnScheme = Ann DictVar CtrScheme
type AnnSchemes = [AnnScheme]

-- | Variable-annotated equality constraints
type AnnEqCt = Ann FcCoVar EqCt
type AnnEqCs = [AnnEqCt]

-- | Variable-annotated equality constraints
data AnnTypeCt = AnnEqCt AnnEqCt | AnnClsCt AnnClsCt
type AnnTypeCs = [AnnTypeCt]

-- | The program theory is just a list of name-annotated constrains
type ProgramTheory = AnnSchemes

-- | TODO doc
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

type GivenCs = [GivenCt]

partitionWantedCs :: WantedCs -> ([WantedEqCt], [WantedClsCt])
partitionWantedCs (WantedEqCt ct:cs) = first (ct :) $ partitionWantedCs cs
partitionWantedCs (WantedClsCt ct:cs) = second (ct :) $ partitionWantedCs cs
partitionWantedCs [] = ([], [])

clsCsToSchemes :: AnnClsCs -> AnnSchemes
clsCsToSchemes = (fmap . fmap) (CtrScheme [] [])

-- | TODO doc
data Axiom = Axiom
  { ax_fc_var :: FcAxVar
  , ax_uv     :: [RnTyVar]
  , ax_ty_fam :: RnTyFam
  , ax_params :: [RnMonoTy]
  , ax_ty     :: RnMonoTy
  }

type Axioms = [Axiom]

data Theory = Theory
  { theory_schemes :: AnnSchemes
  , theory_axioms  :: Axioms
  , theory_givens  :: GivenCs
  }

tExtendAxioms :: Theory -> Axioms -> Theory
tExtendAxioms theory axioms =
  theory { theory_axioms = axioms `mappend` theory_axioms theory }

tExtendSchemes :: Theory -> AnnSchemes -> Theory
tExtendSchemes theory schemes =
  theory { theory_schemes = schemes `mappend` theory_schemes theory }

tExtendGivens :: Theory -> GivenCs -> Theory
tExtendGivens theory givens =
  theory { theory_givens = givens `mappend` theory_givens theory}

tExtendGivenCls :: Theory -> AnnClsCs -> Theory
tExtendGivenCls theory cls_cs =
  theory `tExtendGivens`
  (GivenClsCt <$> ((FcTmVar <$> labelOf cls_cs) |: dropLabel cls_cs))

tExtendGivenEq  :: Theory -> AnnEqCs -> Theory
tExtendGivenEq theory eq_cs =
  theory `tExtendGivens`
  (GivenEqCt <$> ((FcCoVar <$> labelOf eq_cs) |: dropLabel eq_cs))

-- * Collecting Free Variables Out Of Objects
-- ------------------------------------------------------------------------------

-- be bold
instance ContainsFreeTyVars (Ann DictVar RnClsCt) RnTyVar where
  ftyvsOf (_ :| ct) = ftyvsOf ct

instance Eq a => ContainsFreeTyVars (MonoTy a) (HsTyVar a) where
  ftyvsOf = nub . ftyvsOfMonoTy
    where
      -- | Free variables of a monotype (with multiplicities)
      ftyvsOfMonoTy :: MonoTy a -> [HsTyVar a]
      ftyvsOfMonoTy (TyCon {})      = []
      ftyvsOfMonoTy (TyApp ty1 ty2) = ftyvsOfMonoTy ty1 ++ ftyvsOfMonoTy ty2
      ftyvsOfMonoTy (TyVar v)       = [v]
      ftyvsOfMonoTy (TyFam _f tys)  = concatMap ftyvsOfMonoTy tys

instance Eq a => ContainsFreeTyVars (ClsCt a) (HsTyVar a) where
  ftyvsOf (ClsCt _ ty) = ftyvsOf ty

instance ContainsFreeTyVars EqCt RnTyVar where
  ftyvsOf (ty1 :~: ty2) = nub (ftyvsOf ty1 ++ ftyvsOf ty2)

instance Eq a => ContainsFreeTyVars (QualTy a) (HsTyVar a) where
  ftyvsOf (QMono ty)    = ftyvsOf ty
  ftyvsOf (QQual ct ty) = nub (ftyvsOf ct ++ ftyvsOf ty)

instance Eq a => ContainsFreeTyVars (PolyTy a) (HsTyVar a) where
  ftyvsOf (PQual ty)   = ftyvsOf ty
  ftyvsOf (PPoly a ty) = ftyvsOf ty \\ [labelOf a]

-- * Pretty Printing
-- ------------------------------------------------------------------------------

-- | Pretty print a type constructor
instance Symable a => PrettyPrint (HsTyCon a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print type constructor info
instance PrettyPrint HsTyConInfo where
  ppr (HsTCInfo _tc type_args _fc_ty_con proj_funcs)
    = braces $ vcat $ punctuate comma
    $ [
        text "univ"       <+> colon <+> ppr (map (\ty -> ty :| kindOf ty) type_args)
      , text "proj_funcs" <+> colon <+> ppr proj_funcs
      ]
  needsParens _ = False

-- | Pretty print a data constructor
instance Symable a => PrettyPrint (HsDataCon a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print data constructor info
instance PrettyPrint HsDataConInfo where
  ppr (HsDCInfo _dc univs tc arg_tys _dc_fc_data_con)
    = braces $ hsep $ punctuate comma
    $ [
        text "univ"    <+> colon <+> ppr univs
      , text "parent"  <+> colon <+> ppr tc
      , text "arg_tys" <+> colon <+> ppr arg_tys
      ]
  needsParens _ = False

-- | Pretty print class names
instance Symable a => PrettyPrint (Class a) where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print type family info
instance PrettyPrint HsTyFamInfo where
  ppr (HsTFInfo fam type_args kind)
    = braces $ vcat $ punctuate comma
    $ [ text "hs_tf_fam"       <+> colon <+> ppr fam
      , text "hs_tf_type_args" <+> colon <+> ppr type_args
      , text "hs_tf_kind"      <+> colon <+> ppr kind
      ]
  needsParens _ = False

-- | Pretty print type class info
instance PrettyPrint ClassInfo where
  ppr (ClassInfo ab_s cs cls type_args fundeps fd_fams method method_ty tycon datacon)
    = braces $ vcat $ punctuate comma
    $ [ text "cls_abs"       <+> colon <+> ppr ab_s
      , text "cls_super"     <+> colon <+> ppr cs
      , text "cls_class"     <+> colon <+> ppr cls
      , text "cls_type_args" <+> colon <+> ppr type_args
      , text "cls_fundeps"   <+> colon <+> ppr fundeps
      , text "cls_fd_fams"   <+> colon <+> ppr fd_fams
      , text "cls_method"    <+> colon <+> ppr method
      , text "cls_method_ty" <+> colon <+> ppr method_ty
      , text "cls_tycon"     <+> colon <+> ppr tycon
      , text "cls_datacon"   <+> colon <+> ppr datacon
      ]
  needsParens _ = False

-- | Pretty print renamer's type class info
instance PrettyPrint RnClsInfo where
  ppr (RnClsInfo cls method)
    = braces $ vcat $ punctuate comma
    $ [ text "cls_class"     <+> colon <+> ppr cls
      , text "cls_method"    <+> colon <+> ppr method
      ]
  needsParens _ = False

-- | Pretty print terms
instance (Symable a, PrettyPrint a) => PrettyPrint (Term a) where
  ppr (TmVar v)          = ppr v
  ppr (TmCon dc)         = ppr dc
  ppr (TmAbs v tm)       = backslash <> ppr v <> dot <+> ppr tm
  ppr (TmApp tm1 tm2)
    | TmApp {} <- tm1    = ppr tm1    <+> pprPar tm2
    | otherwise          = pprPar tm1 <+> pprPar tm2
  ppr (TmLet v tm1 tm2)  = colorDoc yellow (text "let") <+> ppr v <+> equals <+> ppr tm1
                        $$ colorDoc yellow (text "in")  <+> ppr tm2
  ppr (TmCase scr alts)  = hang (text "case" <+> ppr scr <+> text "of") 2 (vcat $ map ppr alts)

  needsParens (TmAbs  {}) = True
  needsParens (TmApp  {}) = True
  needsParens (TmLet  {}) = True
  needsParens (TmCase {}) = True
  needsParens (TmVar  {}) = False
  needsParens (TmCon  {}) = False

-- | Pretty print monotypes
instance (Symable a, PrettyPrint a) => PrettyPrint (MonoTy a) where
  ppr ty | Just (ty1, ty2) <- isHsArrowTy ty
         = case isHsArrowTy ty1 of
             Just {} -> pprPar ty1 <+> arrow <+> ppr ty2
             Nothing -> ppr ty1    <+> arrow <+> ppr ty2
  ppr (TyCon tc)      = ppr tc
  ppr (TyApp ty1 ty2)
    | TyApp {} <- ty1 = ppr ty1    <+> pprPar ty2
    | otherwise       = pprPar ty1 <+> pprPar ty2
  ppr (TyVar var)     = ppr var
  ppr (TyFam f tys)   = ppr f <> (parens . sep . punctuate comma $ map ppr tys)

  needsParens (TyCon {}) = False
  needsParens (TyApp {}) = True
  needsParens (TyVar {}) = False
  needsParens (TyFam {}) = False

-- | Pretty print qualified types
instance (Symable a, PrettyPrint a) => PrettyPrint (QualTy a) where
  ppr (QMono    ty) = ppr ty
  ppr (QQual ct ty)
    | let dct = pprPar ct --if isClsCtr ct then pprPar ct else ppr ct
    = dct <+> darrow <+> ppr ty

  needsParens (QMono ty) = needsParens ty
  needsParens (QQual {}) = True

-- | Pretty print polytypes
instance (Symable a, PrettyPrint a) => PrettyPrint (PolyTy a) where
  ppr (PQual   ty) = ppr ty
  ppr (PPoly a ty) = forall <> ppr a <> dot <+> ppr ty

  needsParens (PQual ty) = needsParens ty
  needsParens (PPoly {}) = True

-- | Pretty print constraint schemes
instance PrettyPrint CtrScheme where
  ppr (CtrScheme as cs cls) =
    (foldr
       (\a b -> forall <> ppr a <> dot <+> b)
       (pprCs cs <+> ppr cls)
       as)
    where
      pprCs [] = empty
      pprCs cs' = (parens . sep . punctuate comma $ map ppr cs') <+> darrow
  needsParens _ = True

-- | Pretty print class constraints
instance (Symable a, PrettyPrint a) => PrettyPrint (ClsCt a) where
  ppr (ClsCt cls tys) = ppr cls <+> hsep (pprPar <$> tys)
  needsParens _      = True

-- | Pretty print programs
instance (Symable a, PrettyPrint a) => PrettyPrint (Program a) where
  ppr (Program decls) = vcat (ppr <$> decls)

  needsParens _ = False

-- | Pretty print declarations
instance (Symable a, PrettyPrint a) => PrettyPrint (Decl a) where
  ppr (ClsDecl  cdecl) = ppr cdecl
  ppr (InsDecl  idecl) = ppr idecl
  ppr (DataDecl ddecl) = ppr ddecl
  ppr (ValDecl  vdecl) = ppr vdecl

  needsParens _ = False

-- | Pretty print class declarations
instance (Symable a, PrettyPrint a) => PrettyPrint (ClsDecl a) where
  ppr (ClsD cAbs cs cName cVars cFds mName mTy) =
    hang
      (colorDoc green (text "class") <+>
       forall <>
       hsep (ppr <$> cAbs) <>
       dot <+>
       pprCs <+>
       ppr cName <+> hsep (fmap ppr cVars)
       <+> pprFds
       <+> colorDoc green (text "where")
      )
      2
      (ppr (symOf mName) <+> dcolon <+> ppr mTy)
    where
      pprCs =
        if null cs
          then empty
          else (parens . sep $ punctuate comma (ppr <$> cs)) <+> darrow
      pprFds =
        if null cFds
          then empty
          else colorDoc yellow (text "|") <+>
               (hsep . punctuate comma $ fmap ppr cFds)

  needsParens _ = False

-- | Pretty print class instances
instance (Symable a, PrettyPrint a) => PrettyPrint (InsDecl a) where
  ppr (InsD _ cs cName cTy mName mExp)
    = hang (colorDoc green (text "instance") <+> pprCs cs <+> darrow <+> ppr cName <+> pprPar cTy <+> colorDoc green (text "where"))
           2
           (ppr mName <+> equals <+> ppr mExp)
    where
      pprCs = parens . sep . punctuate comma . map ppr

  needsParens _ = False

-- | Pretty print datatype declarations
instance (Symable a, PrettyPrint a) => PrettyPrint (DataDecl a) where
  ppr (DataD tc as dcs) = hsep [colorDoc green (text "data"), ppr tc, hsep (map ppr as), cons]
    where
      ppr_dc (dc, tys) = hsep (colorDoc yellow (char '|') : ppr dc : map pprPar tys)

      cons = sep $ case dcs of
        []               -> []
        ((dc, tys):rest) -> hsep (colorDoc yellow (char '=') : ppr dc : map pprPar tys) : map ppr_dc rest

  needsParens _ = False

-- | Pretty print a top-level value binding
instance (Symable a, PrettyPrint a) => PrettyPrint (ValBind a) where
  ppr (ValBind a m_ty tm) = ppr a <+> pprTy <+> equals <+> ppr tm
    where
      pprTy = case m_ty of
        Nothing -> empty
        Just ty -> dcolon <+> ppr ty
  needsParens _ = False

-- | Pretty print equality constraints
instance PrettyPrint EqCt where
  ppr (ty1 :~: ty2) = ppr ty1 <+> text "~" <+> ppr ty2
  needsParens _ = True

-- | Pretty print functional dependencies
instance (Symable a, PrettyPrint a) => PrettyPrint (Fundep a) where
  ppr (Fundep as b) =
    hsep (fmap ppr as) <+>
    colorDoc yellow (text "->") <+>
    ppr b

  needsParens _ = False

-- | Pretty print axioms
instance PrettyPrint Axiom where
  ppr (Axiom g as f tys ty) =
    ppr g <+>
      parens (sep (punctuate comma (map ppr as))) <+>
      colon <+>
      ppr f <> parens (sep (punctuate comma (map ppr tys))) <+>
      text "~" <+>
      ppr ty
  needsParens _ = True

-- | Pretty print the theory
instance PrettyPrint Theory where
  ppr (Theory schemes axioms givens)
    = braces $ vcat $ punctuate comma
    $ [ text "theory_schemes" <+> colon <+> ppr schemes
      , text "theory_axioms"  <+> colon <+> ppr axioms
      , text "theory_givens"  <+> colon <+> ppr givens
      ]
  needsParens _ = False

-- | Pretty print annotated type constraints
instance PrettyPrint AnnTypeCt where
  ppr (AnnEqCt  ct) = ppr ct
  ppr (AnnClsCt ct) = ppr ct

  needsParens _     = False

-- | TODO doc
instance PrettyPrint WantedCt where
  ppr (WantedEqCt  ct) = ppr ct
  ppr (WantedClsCt ct) = ppr ct
  needsParens _ = False

instance PrettyPrint GivenCt where
  ppr (GivenEqCt  ct) = ppr ct
  ppr (GivenClsCt ct) = ppr ct
  needsParens _ = False
