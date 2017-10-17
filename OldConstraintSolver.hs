
-- | Completely entail a set of constraints. Fail if not possible
entailTcM :: [RnTyVar] -> ProgramTheory -> ProgramTheory -> TcM FcTmSubst
entailTcM untch theory ctrs = runSolverFirstM (go ctrs)
  where
    go SN        = return mempty
    go (cs :> (d :| CtrClsCt cls_ctr)) = do
      (ccs, subst1) <- leftEntailsBacktrack untch theory (d :| cls_ctr )
      subst2 <- go (cs <> ccs)
      return (subst2 <> subst1)

-- | Exhaustively simplify a set of constraints (this version does not backtrack)
entailDetTcM :: [RnTyVar] -> ProgramTheory -> ProgramTheory -> TcM (ProgramTheory, FcTmSubst)
entailDetTcM untch theory ctrs = go ctrs
  where
    entail_one :: AnnCtr -> TcM (Maybe (ProgramTheory, FcTmSubst))
    entail_one = rightEntailsDet untch theory

    go :: ProgramTheory -> TcM (ProgramTheory, FcTmSubst)
    go cs = findSLMaybeM entail_one cs >>= \case
      Just (rest, (simp_cs, subst1)) -> do
        (final_cs, subst2) <- go (rest <> simp_cs)
        return (final_cs, subst2 <> subst1)
      Nothing -> return (cs, mempty)

-- | Performs a single right entailment step.
--   a) fail if the constraint is not entailed by the given program theory
--   b) return the new wanted (class) constraints, as well as the System F term subsitution
rightEntailsDet :: [RnTyVar] -> ProgramTheory -> AnnCtr
                -> TcM (Maybe (ProgramTheory, FcTmSubst))
-- Implication Case
rightEntailsDet untch theory (d0 :| CtrImpl ctr1 ctr2) = do
  d1 <- freshDictVar
  d2 <- freshDictVar

  rightEntailsDet untch (theory :> (d1 :| ctr1)) (d2 :| ctr2) >>= \case
    Just (res_ccs, ev_subst) -> do
      new_ds <- listToSnocList <$> genFreshDictVars (snocListLength res_ccs) -- Fresh dictionary variables (d's), one for each residual constraint

      -- The new residual constraints
      let new_residuals = zipWithSnocList
                            (\d' (_d :| ctr) -> d' :| CtrImpl ctr1 ctr)
                            new_ds
                            res_ccs

      -- The new evidence substitution
      new_ev_subst <- do
        fc_ty1 <- elabCtr ctr1
        let dsubst = foldZipWithSnocList (\d' d -> d |-> FcTmApp (FcTmVar d') (FcTmVar d1))
                                         new_ds
                                         (labelOf res_ccs)
        return (d0 |-> FcTmAbs d1 fc_ty1 (substFcTmInTm (dsubst <> ev_subst) (FcTmVar d2)))

      return (Just (new_residuals, new_ev_subst))
    Nothing -> return Nothing

-- Class Case
rightEntailsDet untch theory (d :| CtrClsCt cls_ct)
  = leftEntailsDet untch theory (d :| cls_ct)

-- | Deterministic left search
leftEntailsDet :: [RnTyVar] -> ProgramTheory -> AnnClsCt
               -> TcM (Maybe (ProgramTheory, FcTmSubst))
leftEntailsDet untch theory cls_ct = lookupSLMaybeM left_entails theory
  where
    left_entails ct = leftEntails untch ct cls_ct

leftEntailsBacktrack :: [RnTyVar] -> ProgramTheory -> AnnClsCt
                     -> SolveM (ProgramTheory, FcTmSubst)
leftEntailsBacktrack untch theory ann_cls_ct = liftSolveM (snocListChooseM theory left_entail) >>= SolveM . selectListT
  where
    left_entail ann_ctr = leftEntails untch ann_ctr ann_cls_ct

-- | Checks whether the class constraint is entailed by the given constraint
--   a) fails if the class constraint is not entailed
--   b) return the new wanted constraints, as well as the System F term substitution
leftEntails :: [RnTyVar] -> AnnCtr -> AnnClsCt
            -> TcM (Maybe (ProgramTheory, FcTmSubst))
leftEntails untch (d :| ctr) cls_ct = do
  freshened_ctr <- freshenLclBndrs ctr
  leftEntailsInt untch (d :| freshened_ctr) cls_ct >>= \case
    Nothing                     -> return Nothing
    Just (rem_ccs, _, ev_subst) -> return $ Just (rem_ccs, ev_subst)

-- | Check whether the class constraint is entailed by the given constraint
-- Identical to the leftEntails function, but also returns the resulting type subsitution
leftEntailsInt :: [RnTyVar] -> AnnCtr -> AnnClsCt
               -> TcM (Maybe (ProgramTheory, HsTySubst, FcTmSubst))
-- Class Case
leftEntailsInt untch (d :| CtrClsCt ct) ann_cls_ct
  = matchClsCs untch (d :| ct) ann_cls_ct

-- Implication Case
leftEntailsInt untch (d :| CtrImpl ctr1 ctr2) ann_cls_ct = do
  d1 <- freshDictVar
  d2 <- freshDictVar
  -- Recursive call
  leftEntailsInt untch (d2 :| ctr2) ann_cls_ct >>= \case
    Nothing                            -> return Nothing
    Just (res_ccs, ty_subst, ev_subst) -> do
      -- Return values
      fresh_ctr1 <- freshenLclBndrs ctr1
      let residual_ccs = res_ccs :> (d1 :| substInCtr ty_subst fresh_ctr1)
      let res_ev_subst = (d2 |-> (FcTmApp (FcTmVar d) (FcTmVar d1))) <> ev_subst
      return $ Just (residual_ccs, ty_subst, res_ev_subst)

-- Universal Quantification Case
leftEntailsInt untch (d :| CtrAbs (var :| _) ctr) ann_cls_ct = do
  d' <- freshDictVar
  -- Recursive call
  leftEntailsInt untch (d' :| ctr) ann_cls_ct >>= \case
    Nothing                            -> return Nothing
    Just (res_ccs, ty_subst, ev_subst) -> do
      -- Return values
      subst_fc_ty  <- elabMonoTy $ substInMonoTy ty_subst (TyVar var)
      let res_ev_subst = (d' |-> (FcTmTyApp (FcTmVar d) subst_fc_ty)) <> ev_subst
      return $ Just (res_ccs, ty_subst, res_ev_subst)

-- | Unify two annotated class constraints (check that they have the same class
-- name and that the arguments can be unified). Return the resulting type and
-- term substitution, as well as the new wanted constraints (always empty).
matchClsCs :: Monad m => [RnTyVar] -> AnnClsCt {- Given -} -> AnnClsCt {- Wanted -}
           -> m (Maybe (ProgramTheory, HsTySubst, FcTmSubst))
matchClsCs untch (d1 :| ClsCt cls1 ty1) (d2 :| ClsCt cls2 ty2)
  | cls1 == cls2
  , Right ty_subst <- unify untch [ty1 :~: ty2]
  = return $ Just (mempty, ty_subst, d2 |-> FcTmVar d1)
  | otherwise = return Nothing

