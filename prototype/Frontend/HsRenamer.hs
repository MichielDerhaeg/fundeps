{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}

module Frontend.HsRenamer (RnEnv(..), hsRename) where

import Frontend.HsTypes
import Backend.FcTypes

import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint
import Utils.Utils
import Utils.Annotated
import Utils.Errors

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

-- * Renaming monad
-- ------------------------------------------------------------------------------

data RnEnv = RnEnv { rn_env_cls_info :: AssocList PsClass   RnClsInfo
                   , rn_env_dc_info  :: AssocList PsDataCon HsDataConInfo
                   , rn_env_tc_info  :: AssocList PsTyCon   HsTyConInfo   }

instance PrettyPrint RnEnv where
  ppr (RnEnv cls_infos dc_infos tc_infos)
    = braces $ vcat $ punctuate comma
    [ text "rn_env_cls_info" <+> colon <+> ppr cls_infos
    , text "rn_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "rn_env_tc_info"  <+> colon <+> ppr tc_infos
    ]
  needsParens _ = False

type RnM = UniqueSupplyT (ReaderT RnCtx (StateT RnEnv (Except CompileError)))

-- * Basic Monadic Setters and Getters
-- ------------------------------------------------------------------------------

-- | Get all renamed class names from the state
getClsInfoRnM :: RnM (AssocList PsClass RnClsInfo)
getClsInfoRnM = rn_env_cls_info <$> get

-- | Get all renamed datacon names from the state
getDataConInfoRnM :: RnM (AssocList PsDataCon HsDataConInfo)
getDataConInfoRnM = rn_env_dc_info <$> get

-- | Get all renamed tycon names from the state
getTyConInfoRnM :: RnM (AssocList PsTyCon HsTyConInfo)
getTyConInfoRnM = rn_env_tc_info <$> get

-- | Lookup the info of a class
lookupClsInfoRnM :: PsClass -> RnM RnClsInfo
lookupClsInfoRnM cls = getClsInfoRnM >>= \cls_infos ->
  case lookupInAssocList cls cls_infos of
    Just cls_info -> return cls_info
    Nothing       -> rnFail (text "Class name" <+> ppr cls <+> text "unbound")

-- | Lookup the info of a data constructor
lookupDataConInfoRnM :: PsDataCon -> RnM HsDataConInfo
lookupDataConInfoRnM dc = getDataConInfoRnM >>= \dc_infos ->
  case lookupInAssocList dc dc_infos of
    Just dc_info -> return dc_info
    Nothing      -> rnFail (text "DataCon name" <+> ppr dc <+> text "unbound")

-- | Lookup the info of a type constructor
lookupTyConInfoRnM :: PsTyCon -> RnM HsTyConInfo
lookupTyConInfoRnM tc = getTyConInfoRnM >>= \tc_infos ->
  case lookupInAssocList tc tc_infos of
    Just tc_info -> return tc_info
    Nothing      -> rnFail (text "TyCon name" <+> ppr tc <+> text "unbound")

-- | Add a renamed class name to the state
addClsInfoRnM :: PsClass -> RnClsInfo -> RnM ()
addClsInfoRnM cls info = modify $ \s ->
  s { rn_env_cls_info = extendAssocList cls info (rn_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoRnM :: PsDataCon -> HsDataConInfo -> RnM ()
addDataConInfoRnM dc info = modify $ \s ->
  s { rn_env_dc_info = extendAssocList dc info (rn_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoRnM :: PsTyCon -> HsTyConInfo -> RnM ()
addTyConInfoRnM tc info = modify $ \s ->
  s { rn_env_tc_info = extendAssocList tc info (rn_env_tc_info s) }

-- | Assign a unique to a plain symbol
rnSym :: MonadUnique m => Sym -> m Name
rnSym s = mkName s <$> getUniqueM

-- | Rename a method name. It has to be unbound
rnMethodName :: PsTmVar -> RnM RnTmVar
rnMethodName x = ask >>= \ctx -> case lookupCtx ctx x of
  Just {} -> rnFail (text "Method name" <+> ppr x <+> text "already bound")
  Nothing -> rnTmVar x

-- | Lookup an already-bound method name
lookupMethodName :: PsTmVar -> RnM RnTmVar
lookupMethodName x = ask >>= \ctx -> case lookupCtx ctx x of
  Just rnx -> return rnx
  Nothing  -> rnFail (text "Method name" <+> ppr x <+> text "unbound")

-- * Rename Types
-- ------------------------------------------------------------------------------

-- | Rename a type variable
rnTyVar :: PsTyVarWithKind -> RnM RnTyVar
rnTyVar (a :| kind) = flip mkRnTyVar kind <$> rnSym (symOf a)

-- | Rename a type pattern and collect the bound variables
rnTyPat :: PsTyPat -> RnM RnTyPat
rnTyPat (HsTyConPat tc)      = HsTyConPat <$> lookupTyCon tc
rnTyPat (HsTyAppPat ty1 ty2) = HsTyAppPat <$> rnTyPat ty1 <*> rnTyPat ty2
rnTyPat (HsTyVarPat a)       = HsTyVarPat <$> lookupCtxM a

-- | Rename a monotype
rnMonoTy :: PsMonoTy -> RnM RnMonoTy
rnMonoTy (TyCon tc)      = TyCon <$> lookupTyCon tc
rnMonoTy (TyApp ty1 ty2) = TyApp <$> rnMonoTy ty1 <*> rnMonoTy ty2
rnMonoTy (TyVar psa)     = TyVar <$> lookupCtxM psa
rnMonoTy  TyFam {}       = error "TODO"

-- | Rename a qualified type
rnQualTy :: PsQualTy -> RnM RnQualTy
rnQualTy (QMono ty)    = QMono <$> rnMonoTy ty
rnQualTy (QQual ct ty) = QQual <$> rnClsCt ct <*> rnQualTy ty

-- | Rename a class constraint
rnClsCt :: PsClsCt -> RnM RnClsCt
rnClsCt (ClsCt cls tys) = ClsCt <$> rnClass cls <*> mapM rnMonoTy tys

-- | Rename a functional dependency
rnFundep :: PsFundep -> RnM RnFundep
rnFundep (Fundep as b) = Fundep <$> mapM lookupCtxM as <*> lookupCtxM b

-- | Rename a class name
rnClass :: PsClass -> RnM RnClass
rnClass cls = do
  cls_infos <- getClsInfoRnM
  case lookupInAssocList cls cls_infos of
    Just cls_info -> return (rn_cls_class cls_info)
    Nothing       -> rnFail (text "Class name" <+> ppr cls <+> text "unbound")

-- | Rename a polytype
rnPolyTy :: PsPolyTy -> RnM RnPolyTy
rnPolyTy (PQual ty)   = PQual <$> rnQualTy ty
rnPolyTy (PPoly a ty) = do
  rna  <- rnTyVar a
  rnty <- extendCtxM (labelOf a) rna (rnPolyTy ty)
  return (PPoly (rna :| kindOf rna) rnty)

-- * Rename Terms
-- ------------------------------------------------------------------------------

-- | Rename a term variable
rnTmVar :: PsTmVar -> RnM RnTmVar
rnTmVar psx = mkRnTmVar <$> rnSym (symOf psx)

-- | Rename a term
rnTerm :: PsTerm -> RnM RnTerm
rnTerm (TmVar x)          = TmVar <$> lookupCtxM x
rnTerm (TmCon dc)         = TmCon <$> lookupDataCon dc
rnTerm (TmAbs psx pstm)   = do
  rnx  <- rnTmVar psx
  rntm <- extendCtxM psx rnx (rnTerm pstm)
  return (TmAbs rnx rntm)
rnTerm (TmApp tm1 tm2)    = TmApp <$> rnTerm tm1 <*> rnTerm tm2
rnTerm (TmLet x tm1 tm2)  = do
  rnx   <- rnTmVar x
  rntm1 <- extendCtxM x rnx (rnTerm tm1)
  rntm2 <- extendCtxM x rnx (rnTerm tm2)
  return (TmLet rnx rntm1 rntm2)
rnTerm (TmCase scr alts)  = TmCase <$> rnTerm scr <*> mapM rnAlt alts

-- | Rename a case alternative
rnAlt :: PsAlt -> RnM RnAlt
rnAlt (HsAlt (HsPat dc xs) tm) = do
  rndc <- lookupDataCon dc
  rnxs <- mapM rnTmVar xs
  let binds = zipExact xs rnxs
  rntm <- extendTmVars binds (rnTerm tm)
  return (HsAlt (HsPat rndc rnxs) rntm)

-- | Rename a type constructor
lookupTyCon :: PsTyCon -> RnM RnTyCon
lookupTyCon tc = hs_tc_ty_con <$> lookupTyConInfoRnM tc

-- | Rename a data constructor
lookupDataCon :: PsDataCon -> RnM RnDataCon
lookupDataCon dc = hs_dc_data_con <$> lookupDataConInfoRnM dc

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTmVars :: [(PsTmVar, RnTmVar)] -> RnM a -> RnM a
extendTmVars binds m = extendCtxM xs xs' m
  where (xs,xs') = unzip binds

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTyVars :: [(PsTyVar, RnTyVar)] -> RnM a -> RnM a
extendTyVars binds m = extendCtxM as as' m
  where (as,as') = unzip binds

-- * Rename Programs and Declarations
-- ------------------------------------------------------------------------------

-- | Rename a class declaration
rnClsDecl :: PsClsDecl -> RnM (RnClsDecl, RnCtx)
rnClsDecl (ClsD bs cs cls as fundeps method method_ty) = do
  -- Rename the class name
  rn_cls <- do
    cls_infos <- getClsInfoRnM
    case lookupInAssocList cls cls_infos of
      Just {} -> rnFail (text "Class" <+> ppr cls <+> text "already defined")
      Nothing -> Class <$> rnSym (symOf cls)

  -- Rename the method name
  rn_method <- rnMethodName method

  -- Store the class info in the global environment
  addClsInfoRnM cls (RnClsInfo rn_cls rn_method)

  -- Rename the type abstractions
  rn_bs <- mapM rnTyVar bs

  -- Rename the class context
  rn_cs <- extendCtxM (labelOf bs) rn_bs (mapM rnClsCt cs)

  -- Rename the type variables
  rn_as <- extendCtxM (labelOf bs) rn_bs $ mapM lookupCtxM as

  -- Rename the functional dependencies
  rn_fundeps <- extendCtxM as rn_as (mapM rnFundep fundeps)

  -- Rename the method type
  rn_method_ty <- extendCtxM as rn_as (rnPolyTy method_ty)

  -- Get the current typing environment (so that we can extend it with the method binding)
  rn_ctx <- ask

  return
    ( ClsD
        (rn_bs |: (kindOf <$> rn_bs))
        rn_cs
        rn_cls
        rn_as
        rn_fundeps
        rn_method
        rn_method_ty
    , extendCtx rn_ctx method rn_method)

-- | Rename an instance declaration
rnInsDecl :: PsInsDecl -> RnM RnInsDecl
rnInsDecl (InsD as cs cls_name typats method_name method_tm) = do
  rn_cls_name     <- rnClass cls_name
  rn_as           <- mapM rnTyVar as
  rn_tys          <- extendCtxM (labelOf as) rn_as (mapM rnTyPat typats)
  rn_cs           <- extendCtxM (labelOf as) rn_as (mapM rnClsCt cs)
  rn_method_name  <- lookupMethodName method_name

  -- Ensure the method name is for the class we are checking
  expected_method_name <- lookupClassMethodName cls_name
  unless (rn_method_name == expected_method_name) $
    rnFail (ppr method_name <+> text "does not belong to class" <+> ppr cls_name)

  rn_method_tm    <- rnTerm method_tm
  return (InsD (rn_as |: (kindOf <$> rn_as)) rn_cs rn_cls_name rn_tys rn_method_name rn_method_tm)

-- | Lookup the name of the method of a particular class
lookupClassMethodName :: PsClass -> RnM RnTmVar
lookupClassMethodName cls = rn_cls_method <$> lookupClsInfoRnM cls

-- | Rename a datatype declaration
rnDataDecl :: PsDataDecl -> RnM RnDataDecl
rnDataDecl (DataD tc as dcs) = do
  -- Rename the type constructor
  rntc <- do
    tc_infos <- getTyConInfoRnM
    case lookupInAssocList tc tc_infos of
      Just {} -> rnFail (text "TyCon" <+> ppr tc <+> text "already defined")
      Nothing -> HsTC <$> rnSym (symOf tc)

  -- Rename the universal type variables
  unless (distinct as) $
    rnFail (text "TyCon" <+> ppr tc <+> text "has non-linear parameters")
  rnas <- mapM rnTyVar as

  -- Store the TyCon info in the global environment
  projs <- forM (zip [0 ..] as) $ \(i, _) ->
      HsTF . mkName (mkSym ("Proj" ++ show (symOf tc) ++ show (i :: Word))) <$>
      getUniqueM
  addTyConInfoRnM tc $ HsTCInfo rntc rnas (FcTC (nameOf rntc)) projs

  -- Rename the data constructors
  let binds = zipExact (map labelOf as) rnas
  rndcs <- forM dcs $ \(dc, tys) -> do
    -- Rename the data constructor
    rndc <- do
      dc_infos <- getDataConInfoRnM
      case lookupInAssocList dc dc_infos of
        Just {} -> rnFail (text "DataCon" <+> ppr dc <+> text "already defined")
        Nothing -> HsDC <$> rnSym (symOf dc)

    -- Rename the data constructor's type arguments
    rntys <- mapM (extendTyVars binds . rnMonoTy) tys

    -- Store the DataCon info in the global environment
    addDataConInfoRnM dc $ HsDCInfo rndc rnas rntc rntys (FcDC (nameOf rndc))

    return (rndc, rntys)

  return (DataD rntc (rnas |: map kindOf rnas) rndcs)

-- | Rename a top-level value binding
rnValBind :: PsValBind -> RnM (RnValBind, RnCtx)
rnValBind (ValBind a m_ty tm) = do
  notInCtxM a
  rn_a <- rnTmVar a
  rn_m_ty <- case m_ty of
    Nothing -> return Nothing
    Just ty -> Just <$> extendCtxM a rn_a (rnPolyTy ty)
  rn_tm <- extendCtxM a rn_a $ rnTerm tm
  ctx <- ask
  return (ValBind rn_a rn_m_ty rn_tm, extendCtx ctx a rn_a)

-- | Rename a program
rnProgram :: PsProgram -> RnM (RnProgram, RnCtx)
rnProgram (PgmExp tm) = do
  rn_tm  <- rnTerm tm
  rn_ctx <- ask
  return (PgmExp rn_tm, rn_ctx)
rnProgram (PgmCls cls_decl pgm) = do
  (rn_cls_decl, ext_ctx) <- rnClsDecl cls_decl
  (rn_pgm, rn_ctx)       <- local (const ext_ctx) $ rnProgram pgm
  return (PgmCls rn_cls_decl rn_pgm, rn_ctx)
rnProgram (PgmInst ins_decl pgm) = do
  rn_ins_decl      <- rnInsDecl ins_decl
  (rn_pgm, rn_ctx) <- rnProgram pgm
  return (PgmInst rn_ins_decl rn_pgm, rn_ctx)
rnProgram (PgmData data_decl pgm) = do
  rn_data_decl <- rnDataDecl data_decl
  (rn_pgm, rn_ctx) <- rnProgram pgm
  return (PgmData rn_data_decl rn_pgm, rn_ctx)
rnProgram (PgmVal val_bind pgm) = do
  (rn_val_bind, ext_ctx) <- rnValBind val_bind
  (rn_pgm, rn_ctx) <- setCtxM ext_ctx $ rnProgram pgm
  return (PgmVal rn_val_bind rn_pgm, rn_ctx)

-- * Invoke the complete renamer
-- ------------------------------------------------------------------------------

hsRename :: UniqueSupply -> PsProgram
         -> Either CompileError (((RnProgram, RnCtx), UniqueSupply), RnEnv)
hsRename us pgm = runExcept
                $ flip runStateT  rn_init_gbl_env
                $ flip runReaderT rn_init_ctx
                $ flip runUniqueSupplyT us
                $ markRnError
                $ rnProgram pgm
  where
    rn_init_ctx     = mempty
    rn_init_gbl_env = RnEnv { rn_env_cls_info = mempty
                            , rn_env_dc_info  = mempty
                            , rn_env_tc_info  = extendAssocList psArrowTyCon arrowTyConInfo mempty
                            }

rnFail :: MonadFail m => Doc -> m a
rnFail = failM . CompileError HsRenamer

markRnError :: MonadError CompileError m => m a -> m a
markRnError = markErrorPhase HsRenamer
