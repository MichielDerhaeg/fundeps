{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Ctx
( Ctx -- Keep opaque
, lookupTyVarCtx, lookupTmVarCtx, extendCtxTy, extendCtxTm
, lookupTyVarM, lookupTmVarM
, extendCtxTyM, extendCtxTysM
, extendCtxTmM, extendCtxTmsM
, extendCtxM, setCtxM
, FcTcCtx, extendCtxM'
, lookupCtxM', notInCtxM
, setCtxM'
) where

import Utils.PrettyPrint hiding ((<>))
import Utils.Errors
import Utils.Var
import Utils.SnocList
import Utils.Kind

import Backend.FcTypes

import Data.Monoid
import Control.Monad.Reader
import Control.Monad.Except

-- | All kinds of contexts. E.g. used for
--   a) source renaming environment
--   b) source typing environment
--   c) target typing environment

data Ctx tm_var tm_assoc ty_var ty_assoc
  = CtxNil                                                          -- ^ Empty context
  | CtxConsTm (Ctx tm_var tm_assoc ty_var ty_assoc) tm_var tm_assoc -- ^ Term binding
  | CtxConsTy (Ctx tm_var tm_assoc ty_var ty_assoc) ty_var ty_assoc -- ^ Type binding

instance ( PrettyPrint tm_var, PrettyPrint tm_assoc
         , PrettyPrint ty_var, PrettyPrint ty_assoc
         ) => PrettyPrint (Ctx tm_var tm_assoc ty_var ty_assoc) where
  ppr = brackets . fsep . punctuate comma . reverse . ctxToList
    where
      ctxToList CtxNil                          = []
      ctxToList (CtxConsTm ctx tm_var tm_assoc) = (ppr tm_var <+> colon <+> ppr tm_assoc) : ctxToList ctx
      ctxToList (CtxConsTy ctx ty_var ty_assoc) = (ppr ty_var <+> colon <+> ppr ty_assoc) : ctxToList ctx
  needsParens _ = False

instance Monoid (Ctx tm_var tm_assoc ty_var ty_assoc) where
  mempty = CtxNil

  mappend ctx CtxNil            = ctx
  mappend ctx (CtxConsTm c v t) = CtxConsTm (mappend ctx c) v t
  mappend ctx (CtxConsTy c v t) = CtxConsTy (mappend ctx c) v t

  mconcat = foldl mappend CtxNil -- foldl since mappend does induction on the second argument

-- | Lookup a type variable binding
lookupTyVarCtx :: Eq a => Ctx x x' a a' -> a -> Maybe a'
lookupTyVarCtx CtxNil                 _a = Nothing
lookupTyVarCtx (CtxConsTm ctx _x _x')  a = lookupTyVarCtx ctx a
lookupTyVarCtx (CtxConsTy ctx  b  b')  a = if a == b then Just b' else lookupTyVarCtx ctx a

-- | Lookup a term variable binding
lookupTmVarCtx :: Eq x => Ctx x x' a a' -> x -> Maybe x'
lookupTmVarCtx CtxNil                 _x = Nothing
lookupTmVarCtx (CtxConsTm ctx  y  y')  x = if x == y then Just y' else lookupTmVarCtx ctx x
lookupTmVarCtx (CtxConsTy ctx _b _b')  x = lookupTmVarCtx ctx x

-- | Extend the context with a type binding
extendCtxTy :: Ctx x x' a a' -> a -> a' -> Ctx x x' a a'
extendCtxTy ctx tv ty = CtxConsTy ctx tv ty

-- | Extend the context with a term binding
extendCtxTm :: Ctx x x' a a' -> x -> x' -> Ctx x x' a a'
extendCtxTm ctx tv tm = CtxConsTm ctx tv tm

-- | Lookup a type variable in the context
lookupTyVarM :: (Eq a, PrettyPrint a, MonadReader (Ctx x x' a b) m, MonadError CompileError m) => a -> m b
lookupTyVarM psb = ask >>= \ctx -> case lookupTyVarCtx ctx psb of
  Just rnb -> return rnb
  Nothing  -> throwErrorM (text "Unbound type variable" <+> colon <+> ppr psb)

-- | Lookup a term variable in the context
lookupTmVarM :: (Eq a1, PrettyPrint a1, MonadReader (Ctx a1 b a a') m, MonadError CompileError m) => a1 -> m b
lookupTmVarM psy = ask >>= \ctx -> case lookupTmVarCtx ctx psy of
  Just rny -> return rny
  Nothing  -> throwErrorM (text "Unbound term variable" <+> colon <+> ppr psy)

-- | Add a type variable to the context
extendCtxTyM :: MonadReader (Ctx x x' a a') m => a -> a' -> m b -> m b
extendCtxTyM psa rna = local (\ctx -> extendCtxTy ctx psa rna)

-- | Add many type variables to the context
extendCtxTysM :: (MonadReader (Ctx x x' a a') m, MonadError CompileError m) => [a] -> [a'] -> m b -> m b
extendCtxTysM []     []     m = m
extendCtxTysM (a:as) (b:bs) m = extendCtxTyM a b (extendCtxTysM as bs m)
extendCtxTysM _      _      _ = throwErrorM (text "extendCtxTysM" <+> colon <+> text "length mismatch")

-- | Add a term variable to the context
extendCtxTmM :: MonadReader (Ctx x x' a a') m => x -> x' -> m b -> m b
extendCtxTmM psx rnx = local (\ctx -> extendCtxTm ctx psx rnx)

-- | Add many term variables to the context
extendCtxTmsM :: (MonadReader (Ctx x x' a a') m, MonadError CompileError m) => [x] -> [x'] -> m b -> m b
extendCtxTmsM []     []     m = m
extendCtxTmsM (x:xs) (y:ys) m = extendCtxTmM x y (extendCtxTmsM xs ys m)
extendCtxTmsM _      _      _ = throwErrorM (text "extendCtxTmsM" <+> colon <+> text "length mismatch")

-- | Extend the context with a context extension
extendCtxM :: (Monoid r, MonadReader r m) => r -> m a -> m a
extendCtxM ctx2 = local (\ctx1 -> ctx1 <> ctx2)

-- | Replace the context
setCtxM :: MonadReader r m => r -> m a -> m a
setCtxM ctx = local (\_ -> ctx)

class (Eq src) => Context ctx src trg | src ctx -> trg where
  lookupCtx :: ctx -> src -> Maybe trg
  extendCtx :: ctx -> src -> trg -> ctx

lookupCtxM' ::
     ( MonadError CompileError m
     , PrettyPrint src
     , Context ctx src trg
     , MonadReader ctx m
     )
  => src
  -> m trg
lookupCtxM' src = ask >>= \ctx -> case lookupCtx ctx src of
  Just trg -> return trg
  Nothing -> throwErrorM $ text "Unbound variable" <+> colon <+> ppr src

extendCtxM' :: (Context ctx src trg, MonadReader ctx m) => src -> trg -> m a -> m a
extendCtxM' s t = local (\ctx -> extendCtx ctx s t)

setCtxM' :: MonadReader ctx m => ctx -> m a -> m a
setCtxM' ctx = local (\_ -> ctx)

notInCtxM ::
     ( PrettyPrint src
     , MonadReader ctx m
     , MonadError CompileError m
     , Context ctx src trg
     )
  => src
  -> m ()
notInCtxM x = ask >>= \ctx -> case lookupCtx ctx x of
  Just _ -> throwErrorM (text "notInCtxM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- TODO move FcTc stuff to Fc typechecker?
type FcTcCtx     = SnocList FcTcBinding
data FcTcBinding = FcTcTmBnd FcTmVar FcType
                 | FcTcTyBnd FcTyVar Kind
                 | FcTcCoBnd FcCoVar FcProp

instance Context ctx src trg => Context ctx [src] [trg] where
  lookupCtx ctx as = sequence $ fmap (lookupCtx ctx) as
  extendCtx ctx (s:ss) (t:ts) = extendCtx (extendCtx ctx ss ts) s t
  extendCtx ctx []     []     = ctx
  extendCtx _   _      _      = error "extendCtx: length mismatch"
  -- TODO length mismatch, implement als fooM instead for better error?

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
