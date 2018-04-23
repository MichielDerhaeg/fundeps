module Frontend.FunDep
  ( determinacy
  ) where

import           Frontend.TcMonad
import           Frontend.HsTypes

import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint    hiding ((<>))
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var

import           Control.Monad (forM)
import           Data.Either   (partitionEithers)
import           Data.Monoid   ((<>))

-- * Determinacy
-- ------------------------------------------------------------------------------

-- | Determinacy relation
determinacy :: [RnTyVar] -> RnClsCs -> TcM HsTySubst
determinacy as cls_cs = go cls_cs mempty
  where
    go cs ty_subst = do
      (residual_cs, new_substs) <-
        partitionEithers <$> mapM (det_step ty_subst) cs
      if null new_substs then return ty_subst else
        go residual_cs (ty_subst <> mconcat new_substs)

    det_step ty_subst ct@(ClsCt cls tys) = do
      as' <- lookupClsParams cls
      fds <- lookupClsFundeps cls
      fd_fams <- lookupClsFDFams cls
      let cls_var_subst = buildSubst $ zipExact as' tys
      new_subst <- fmap mconcat $
        forM (zip fds fd_fams) $ \(Fundep bs b0, fam) -> do
          let (t0:ts) = substInMonoTy cls_var_subst . TyVar <$> (b0 : bs)
          let refined_ts = substInMonoTy ty_subst <$> ts
          let as_dom = as <> substDom ty_subst
          if any (`elem` as_dom) (ftyvsOf t0) ||
             not (all (`elem` as_dom) $ ftyvsOf ts)
            then return mempty
            else mconcat . map (\(fv, proj) -> fv |-> proj (TyFam fam refined_ts)) <$>
                 projection t0
      return $ if nullSubst new_subst then Left ct else Right new_subst

-- | Gather type variables and compute their corresponding projection function
projection :: RnMonoTy -> TcM [(RnTyVar, RnMonoTy -> RnMonoTy)]
projection = go id
  where
    go f ty =
      case ty of
        app@(TyApp _ _) -> do
          (tc, tys) <- destructTyApp app
          ty_fams <- lookupTyConProj tc
          concat <$>
            mapM
              (\(ty_fam, app_ty) -> go (\x -> f (TyFam ty_fam [x])) app_ty)
              (zip ty_fams tys)
        TyVar a   -> return [(a, f)]
        TyCon _   -> return []
        TyFam _ _ -> tf_error

    destructTyApp (TyApp ty1 ty2) = do
      (tc, tys) <- destructTyApp ty1
      return (tc, tys ++ [ty2])
    destructTyApp (TyCon tc) = return (tc, [])
    destructTyApp TyFam {} = tf_error
    destructTyApp (TyVar _a) =
      throwErrorM $
      text "projection" <+>
      colon <+> text "Type variable applications are not yet supported"

    tf_error =
      throwErrorM $
      text "projection" <+> colon <+> text "encountered type family"