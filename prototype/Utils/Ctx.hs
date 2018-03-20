{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Ctx
  ( FcTcCtx
  , extendCtxM
  , lookupCtxM
  , notInCtx
  , unboundElemsOf
  , notInCtxM
  , setCtxM
  , RnCtx
  , extendCtx
  , lookupCtx
  , TcCtx
  , FcCoCtx
  ) where

import           Backend.FcTypes
import           Frontend.HsTypes

import           Utils.Errors
import           Utils.FreeVars
import           Utils.Kind
import           Utils.PrettyPrint
import           Utils.SnocList
import           Utils.Var

import           Control.Monad.Except
import           Control.Monad.Reader

-- * Context operations
-- ------------------------------------------------------------------------------

-- | Context type class
class (Eq src) => Context ctx src trg | src ctx -> trg where
  lookupCtx :: ctx -> src -> Maybe trg
  extendCtx :: ctx -> src -> trg -> ctx

-- | Do a lookup in the context, throw an error if not bound
lookupCtxM ::
     ( MonadError CompileError m
     , PrettyPrint src
     , Context ctx src trg
     , MonadReader ctx m
     )
  => src
  -> m trg
lookupCtxM src = ask >>= \ctx -> case lookupCtx ctx src of
  Just trg -> return trg
  Nothing -> throwErrorM $ text "Unbound variable" <+> colon <+> ppr src

-- | Extend the context
extendCtxM :: (Context ctx src trg, MonadReader ctx m) => src -> trg -> m a -> m a
extendCtxM s t = local (\ctx -> extendCtx ctx s t)

-- | Replace the current context
setCtxM :: MonadReader ctx m => ctx -> m a -> m a
setCtxM ctx = local $ const ctx

-- | Check if something is not already bound in the context
notInCtx :: Context ctx src trg => ctx -> src -> Bool
notInCtx ctx src = case lookupCtx ctx src of
  Just _  -> False
  Nothing -> True

-- | Get all the free type variables that are not bound in the context
unboundElemsOf ::
     (Context ctx src trg, MonadReader ctx m, ContainsFreeTyVars t src)
  => t
  -> m [src]
unboundElemsOf t = ask >>= \ctx ->
   return $ filter (notInCtx ctx) (ftyvsOf t)

-- | Check if something is not already bound in the context, throw an error otherwise
notInCtxM ::
     ( PrettyPrint src
     , MonadReader ctx m
     , MonadError CompileError m
     , Context ctx src trg
     )
  => src
  -> m ()
notInCtxM x = ask >>= \ctx -> case lookupCtx ctx x of
  Just _ -> throwErrorM $
    text "notInCtxM" <> colon <+>
      quotes (ppr x) <+> text "is already bound"
  Nothing -> return ()

-- | Context instance for lists
instance Context ctx src trg => Context ctx [src] [trg] where
  lookupCtx ctx               = traverse (lookupCtx ctx)
  extendCtx ctx (s:ss) (t:ts) = extendCtx (extendCtx ctx ss ts) s t
  extendCtx ctx []     []     = ctx
  extendCtx _   _      _      = error "extendCtx: length mismatch"
  -- TODO length mismatch, implement als fooM instead for better error?

-- * System Fc typechecker context
-- ------------------------------------------------------------------------------
type FcTcCtx     = SnocList FcTcBinding
data FcTcBinding = FcTcTmBnd FcTmVar FcType
                 | FcTcTyBnd FcTyVar Kind
                 | FcTcCoBnd FcCoVar FcProp

instance Context (SnocList FcTcBinding) FcTmVar FcType where
  lookupCtx (ctx :> FcTcTmBnd a ty) b = if a == b then Just ty else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcTmBnd src trg

instance Context (SnocList FcTcBinding) FcTyVar Kind where
  lookupCtx (ctx :> FcTcTyBnd a k) b = if a == b then Just k else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcTyBnd src trg

instance Context (SnocList FcTcBinding) FcCoVar FcProp where
  lookupCtx (ctx :> FcTcCoBnd a phi) b = if a == b then Just phi else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcCoBnd src trg

-- * Renamer context
-- ------------------------------------------------------------------------------
type RnCtx = SnocList RnBinding
data RnBinding = RnTmVarBnd PsTmVar RnTmVar
               | RnTyVarBnd PsTyVar RnTyVar

instance Context RnCtx PsTmVar RnTmVar where
  lookupCtx (ctx :> RnTmVarBnd a a') b = if a == b then Just a' else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> RnTmVarBnd src trg

instance Context RnCtx PsTyVar RnTyVar where
  lookupCtx (ctx :> RnTyVarBnd a a') b = if a == b then Just a' else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> RnTyVarBnd src trg

-- * Haskell typechecker context
-- ------------------------------------------------------------------------------
type TcCtx = SnocList TcBinding
data TcBinding = TcTmVarBnd RnTmVar RnPolyTy
               | TcTyVarBnd RnTyVar Kind

instance Context TcCtx RnTmVar RnPolyTy where
  lookupCtx (ctx :> TcTmVarBnd a ty) b = if a == b then Just ty else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> TcTmVarBnd src trg

instance Context TcCtx RnTyVar Kind where
  lookupCtx (ctx :> TcTyVarBnd a k) b = if a == b then Just k else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> TcTyVarBnd src trg

-- * System Fc simplifier context
-- ------------------------------------------------------------------------------

type FcCoCtx = SnocList FcCoBinding
data FcCoBinding = FcCoBinding FcCoVar FcProp

instance Context FcCoCtx FcCoVar FcProp where
  lookupCtx (ctx :> FcCoBinding a psi) b = if a == b then Just psi else lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcCoBinding src trg
