entailCs :: [RnTyVar] -> Theory -> AnnTypeCs -> TcM (AnnTypeCs, HsTySubst, EvSubst)
entailCs untchs theory cs =
  go (entailCt untchs theory) cs >>= \case
    Nothing -> return (cs, mempty, mempty)
    Just ((new_cs, ty_subst, ev_subst), cs') -> do
      (cs'', ty_subst', ev_subst') <-
        entailCs untchs theory (substInAnnTypeCs ty_subst (new_cs <> cs'))
      return (cs'', ty_subst' <> ty_subst, ev_subst' <> ev_subst)
  where
   go :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe (b, [a]))
   go _f []     = return Nothing
   go  f (x:xs) = f x >>= \case
     Just y  -> return $ Just (y,xs)
     Nothing -> (fmap . fmap) (second (x:)) (go f xs)

entailCt :: [RnTyVar] -> Theory -> AnnTypeCt -> TcM (Maybe (AnnTypeCs, HsTySubst, EvSubst))
entailCt untchs theory (AnnEqCt ct) =
  entailEq untchs (theory_axioms theory) ct >>= \case
    Nothing -> return Nothing
    Just (eq_cs, ty_subst, co_subst) ->
      return $ Just (AnnEqCt <$> eq_cs, ty_subst, coToEvSubst co_subst)
entailCt untchs theory (AnnClsCt ct) =
  entailReduce (theory_axioms theory) ct >>= \case
    Just (cls_ct, tm_subst) ->
      return $ Just ([AnnClsCt cls_ct], mempty, tmToEvSubst tm_subst)
    Nothing -> entailCls untchs (theory_schemes theory) ct >>= \case
      Nothing -> return Nothing
      Just (cls_cs, tm_subst) ->
        return $ Just (AnnClsCt <$> cls_cs, mempty, tmToEvSubst tm_subst)

-- | Entail a single type class constraint. Returns Nothing if nothing has been
--   done. May produce additional class constraints.
entailCls :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (Maybe (AnnClsCs, FcTmSubst))
entailCls _untch [] _cls_ct = return Nothing
entailCls as ((d' :| CtrScheme bs cls_cs (ClsCt cls2 tys2)):schemes) ct@(d :| ClsCt cls1 tys1)
  | cls1 == cls2
  , Right ty_subst <- unify as (zipWithExact (:~:) tys1 tys2) = do
    (d''s, ann_cls_cs) <- annotateClsCs $ substInClsCs ty_subst cls_cs
    let fc_subbed_bs = map elabMonoTy . substInTyVars ty_subst $ labelOf bs
    let ev_subst =
          d |->
           foldl
             FcTmApp
             (foldl FcTmTyApp (FcTmVar d') fc_subbed_bs)
             (FcTmVar <$> d''s)
    return $ Just (ann_cls_cs, ev_subst)
  | otherwise = entailCls as schemes ct

entailReduce :: Axioms -> AnnClsCt -> TcM (Maybe (AnnClsCt, FcTmSubst))
entailReduce axioms (d :| ClsCt cls tys) =
  case reduceAll axioms tys of
    Nothing -> return Nothing
    Just (tys', cos') -> do
      d' <- freshDictVar
      tc <- lookupClsTyCon cls
      let co = foldl FcCoApp (FcCoRefl (FcTyCon tc)) (FcCoSym <$> cos')
      return $ Just (d' :| ClsCt cls tys', d |-> FcTmCast (FcTmVar d') co)

-- | Equality contstraint entailment
entailEq :: [RnTyVar] -> Axioms -> AnnEqCt
         -> TcM (Maybe (AnnEqCs, HsTySubst, FcCoSubst))
entailEq untchs p ct = step ct
  where
    step (c :| (TyVar a :~: TyVar b))
      | a == b =
        return $ Just (mempty, mempty, c |-> FcCoRefl (elabMonoTy (TyVar a)))
    step (c :| (TyCon tc1 :~: TyCon tc2))
      | tc1 == tc2 =
        return $ Just (mempty, mempty, c |-> FcCoRefl (elabMonoTy (TyCon tc1)))
      | otherwise = unify_fail
    step (c :| (TyVar a :~: ty))
      | a `notElem` untchs, a `doesNotOccurIn` ty = unify_var c a ty
    step (c :| (ty :~: TyVar a))
      | a `notElem` untchs, a `doesNotOccurIn` ty = unify_var c a ty
    step (_ :| (TyVar _ :~: _)) = return Nothing
    step (_ :| (_ :~: TyVar _)) = return Nothing
    step (c :| (ty_fam@TyFam {} :~: ty))
      | Just (ty', co) <- reduce p ty_fam = unify_fam ty' ty c co
    step (c :| (ty :~: ty_fam@TyFam {}))
      | Just (ty', co) <- reduce p ty_fam = unify_fam ty' ty c co
    step (_ :| (TyFam _ _ :~: _)) = return Nothing
    step (_ :| (_ :~: TyFam _ _)) = return Nothing
    step (c :| (TyApp ty1 ty2 :~: TyApp ty1' ty2')) = do
      [c1, c2] <- replicateM 2 freshFcCoVar
      return $
        Just
          ( [c1 :| (ty1 :~: ty1'), c2 :| (ty2 :~: ty2')]
          , mempty
          , c |-> FcCoApp (FcCoVar c1) (FcCoVar c2))
    step (_ :| (TyCon {} :~: TyApp {})) = unify_fail
    step (_ :| (TyApp {} :~: TyCon {})) = unify_fail

    unify_var c a ty =
      return $ Just (mempty, (a |-> ty), (c |-> FcCoRefl (elabMonoTy ty)))

    unify_fam ty' ty c co = do
      c' <- freshFcCoVar
      return $
        Just ([c' :| (ty' :~: ty)], mempty, (c |-> FcCoTrans co (FcCoVar c')))

    unify_fail = tcFail $ vcat
        [ text "Equality contraint entailment failed."
        , text "Constraints"  <+> colon <+> ppr ct
        , text "Untouchables" <+> colon <+> ppr untchs
        ]

-- | Type reduction
reduce :: Axioms -> RnMonoTy -> Maybe (RnMonoTy, FcCoercion)
reduce axioms = go
  where
    go arg =
      case step arg of
        Nothing -> Nothing
        Just (new_arg, co) ->
          case go new_arg of
            Nothing               -> Just (new_arg, co)
            Just (newer_arg, co') -> Just (newer_arg, FcCoTrans co co')

    step = \case
      TyApp ty1 ty2 -> do
        ([ty1',ty2'],[co1,co2]) <- reduceAll axioms [ty1, ty2]
        return (TyApp ty1' ty2', FcCoApp co1 co2)
      TyCon _tc -> Nothing
      TyVar _x  -> Nothing
      TyFam f tys ->
        case reduceAll axioms tys of
          Just (tys', cos') -> Just (TyFam f tys', FcCoFam (rnTyFamToFcFam f) cos')
          Nothing -> findJust (matchAxiom f tys <$> axioms)

    matchAxiom :: RnTyFam -> [RnMonoTy] -> Axiom -> Maybe (RnMonoTy, FcCoercion)
    matchAxiom f1 tys (Axiom g as f2 us ty)
      | f1 == f2
      , Right subst <- unify as (zipWithExact (:~:) us tys) =
        Just
          ( applySubst subst ty
          , FcCoAx g (elabMonoTy . substInMonoTy subst . TyVar <$> as))
      | otherwise = Nothing

reduceAll :: Axioms -> [RnMonoTy] -> Maybe ([RnMonoTy],[FcCoercion])
reduceAll axioms tys =
  if any isJust m_reds
    then Just $ unzip (uncurry reduceOrReflect <$> zip tys m_reds)
    else Nothing
  where
    m_reds = reduce axioms <$> tys
    reduceOrReflect _ty (Just (new_ty, co)) = (new_ty,co)
    reduceOrReflect ty Nothing = (ty, FcCoRefl (elabMonoTy ty))

