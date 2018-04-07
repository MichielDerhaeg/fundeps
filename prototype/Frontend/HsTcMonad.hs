{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}

module Frontend.HsTcMonad where

import           Frontend.HsTypes

import           Backend.FcTypes

import           Utils.AssocList
import           Utils.Ctx
import           Utils.Errors
import           Utils.Kind
import           Utils.PrettyPrint    hiding ((<>))
import           Utils.Unique
import           Utils.Var

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

-- * Type Checking Monad
-- ------------------------------------------------------------------------------

type TcM = UniqueSupplyT (ReaderT TcCtx (StateT TcEnv (Except CompileError)))

data TcEnv = TcEnv
  { tc_env_cls_info :: AssocList RnClass   ClassInfo
  , tc_env_dc_info  :: AssocList RnDataCon HsDataConInfo
  , tc_env_tc_info  :: AssocList RnTyCon   HsTyConInfo
  , tc_env_tf_info  :: AssocList RnTyFam   HsTyFamInfo
  }

instance PrettyPrint TcEnv where
  ppr (TcEnv cls_infos dc_infos tc_infos tf_infos)
    = braces $ vcat $ punctuate comma
    [ text "tc_env_cls_info" <+> colon <+> ppr cls_infos
    , text "tc_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "tc_env_tc_info"  <+> colon <+> ppr tc_infos
    , text "tc_env_tf_info"  <+> colon <+> ppr tf_infos
    ]
  needsParens _ = False

-- * Add data to the environment
-- ------------------------------------------------------------------------------

-- | Add a renamed class name to the state
addClsInfoTcM :: RnClass -> ClassInfo -> TcM ()
addClsInfoTcM cls info = modify $ \s ->
  s { tc_env_cls_info = extendAssocList cls info (tc_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoTcM :: RnDataCon -> HsDataConInfo -> TcM ()
addDataConInfoTcM dc info = modify $ \s ->
  s { tc_env_dc_info = extendAssocList dc info (tc_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoTcM :: RnTyCon -> HsTyConInfo -> TcM ()
addTyConInfoTcM tc info = modify $ \s ->
  s { tc_env_tc_info = extendAssocList tc info (tc_env_tc_info s) }

-- | Add a renamed tyfam name to the state
addTyFamInfoTcM :: RnTyFam -> HsTyFamInfo -> TcM ()
addTyFamInfoTcM tf info = modify $ \s ->
  s { tc_env_tf_info = extendAssocList tf info (tc_env_tf_info s)}

-- * Lookup data and type constructors for a class
-- ------------------------------------------------------------------------------

-- GEORGE: 1. Rename TcEnv to TcGblEnv
--         2. It's exactly the same as lookupFcGblEnv. Abstract over both.

-- | Lookup something in the global environment
lookupTcEnvM ::
     (Eq a, PrettyPrint a, MonadError CompileError m, MonadState s m)
  => (s -> AssocList a b)
  -> a
  -> m b
lookupTcEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> throwErrorM (text "lookupTcEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup a type constructor
lookupTyCon :: RnTyCon -> TcM FcTyCon
lookupTyCon tc = hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc

-- | Lookup the kind of a type constructor
tyConKind :: RnTyCon -> TcM Kind
tyConKind tc = do
  info <- lookupTcEnvM tc_env_tc_info tc
  return (mkArrowKind (map kindOf (hs_tc_type_args info)) KStar)

-- | Lookup a data constructor
lookupDataCon :: RnDataCon -> TcM FcDataCon
lookupDataCon dc = hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc

-- | Lookup the kinds of the arguments
clsArgKinds :: RnClass -> TcM [Kind]
clsArgKinds cls = map kindOf . cls_type_args <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc type constructor for a class
lookupClsTyCon ::
     (MonadState TcEnv m, MonadError CompileError m) => RnClass -> m FcTyCon
lookupClsTyCon cls = cls_tycon <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc data constructor for a class
lookupClsDataCon :: RnClass -> TcM FcDataCon
lookupClsDataCon cls = cls_datacon <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the signature of a data constructor in pieces
dataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
dataConSig dc = lookupTcEnvM tc_env_dc_info dc >>= \info ->
  return ( hs_dc_univ    info
         , hs_dc_arg_tys info
         , hs_dc_parent  info )

-- | Get the type parameters of the class
lookupClsParams :: RnClass -> TcM [RnTyVar]
lookupClsParams cls = cls_type_args <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the functional dependencies of the class
lookupClsFundeps :: RnClass -> TcM [RnFundep]
lookupClsFundeps cls = cls_fundeps <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the super classes of the class
lookupClsSuper :: RnClass -> TcM RnClsCs
lookupClsSuper cls = cls_super <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the projection type families of the type constructor
lookupTyConProj :: RnTyCon -> TcM [RnTyFam]
lookupTyConProj tc = hs_tc_projs <$> lookupTcEnvM tc_env_tc_info tc

-- | Get the type families of the functional dependencies of the type class
lookupClsFDFams :: RnClass -> TcM [RnTyFam]
lookupClsFDFams cls = cls_fd_fams <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the type family information
lookupTyFamInfo ::
     (MonadState TcEnv m, MonadError CompileError m) => RnTyFam -> m HsTyFamInfo
lookupTyFamInfo f = lookupTcEnvM tc_env_tf_info f

-- | Get the type family return kind
lookupTyFamKind ::
     (MonadError CompileError f, MonadState TcEnv f) => RnTyFam -> f Kind
lookupTyFamKind f = hs_tf_kind <$> lookupTyFamInfo f

-- | Get the type arguments of the type constructor
lookupTyConArgs :: RnTyCon -> TcM [RnTyVar]
lookupTyConArgs tc = hs_tc_type_args <$> lookupTcEnvM tc_env_tc_info tc

-- | Get the parent type constructor of the data constructor
lookupDataConTyCon :: RnDataCon -> TcM RnTyCon
lookupDataConTyCon dc = hs_dc_parent <$> lookupTcEnvM tc_env_dc_info dc
