module Frontend.FunDep
  ( determinacy
  , instantiateFDs
  , instantiateFDsClose
  ) where

import           Frontend.TcMonad
import           Frontend.HsTypes

import           Utils.Errors
import           Utils.FreeVars
import           Utils.PrettyPrint
import           Utils.Substitution
import           Utils.Utils
import           Utils.Var
import           Utils.Kind

import           Control.Monad (forM)
import           Data.Either   (partitionEithers)
import           Data.Semigroup

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

    det_step ty_subst ct = do
      inst_fds <- instantiateFDsClose ct
      new_subst <- fmap mconcat $
        forM inst_fds $ \(fam, ts, t0) -> do
          let refined_ts = substInMonoTy ty_subst <$> ts
          let as_dom = as <> substDom ty_subst
          if any (`elem` as_dom) (ftyvsOf t0) ||
             not (all (`elem` as_dom) $ ftyvsOf ts)
            then return mempty
            else projection t0 (TyFam fam refined_ts)
      return $ if nullSubst new_subst then Left ct else Right new_subst

-- | Gather type variables and compute their corresponding projected types
projection :: RnMonoTy -> RnMonoTy -> TcM HsTySubst
projection ty proj_ty =
  case ty of
    app@(TyApp _ _) -> do
      (tc, tys) <- destructTyApp app
      ty_fams <- lookupTyConProj tc
      mconcat <$>
        mapM
          (\(ty_fam, app_ty) -> projection app_ty (TyFam ty_fam [proj_ty]))
          (zipExact ty_fams tys)
    TyVar a   -> return (a |-> proj_ty)
    TyCon _   -> return mempty
    TyFam _ _ -> tf_error
  where
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

-- | Instantiates the FD's of the given class constraint.
-- Returns 1) the corresponding type family
--         2) the instantiated domain
--         3) the instantiated range
instantiateFDs :: RnClsCt -> TcM [(RnTyFam, [RnMonoTy], RnMonoTy)]
instantiateFDs (ClsCt cls tys) = do
  as <- lookupClsParams cls
  fds <- lookupClsFundeps cls
  fd_fams <- lookupClsFDFams cls
  let cls_var_subst = buildSubst $ zipExact as tys
  return $ zipWithExact (f cls_var_subst) fds fd_fams
  where
    f subst (Fundep bs b0) fam =
      (fam, substInMonoTy subst . TyVar <$> bs, substInMonoTy subst $ TyVar b0)

-- | Instantiates the FD's of the given class constraint,
-- including those of the superclass relation.
instantiateFDsClose :: RnClsCt -> TcM [(RnTyFam, [RnMonoTy], RnMonoTy)]
instantiateFDsClose ct@(ClsCt cls tys) = do
  inst_fds <- instantiateFDs ct
  bs       <- lookupClsExist cls
  super_cs <- lookupClsSuper cls
  as       <- lookupClsParams cls
  bs' <- mapM freshRnTyVar (kindOf <$> bs)
  more_inst_fds <-
    fmap concat $
    forM super_cs $ \(ClsCt cls' tys') -> do
      let subst = buildSubst $ zipExact as tys <> zipExact bs (TyVar <$> bs')
      let inst_cs = ClsCt cls' (substInMonoTy subst <$> tys')
      instantiateFDsClose inst_cs
  return $ inst_fds <> more_inst_fds
