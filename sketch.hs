unify :: MonadError String m => [RnTyVar] -> EqCs -> m HsTySubst

data Impl = MkImpl [RnTyVar] [ClsCt] ClsCt

entail :: [RnTyVar] -> ProgramTheory -> ClsCt -> Maybe [ClsCt]
entail _as SN          _ct = Nothing
entail  as (axs :> ax)  ct = case (ax, ct) of
  (Impl bs qs (ClsCt t1), ClsCt t2) -> case unify as [t1 :~: t2] of
    Nothing    -> entail as axs ct
    Just subst -> Just (map (applyTySubst subst) qs)

simplify :: [RnTyVar] -> ProgramTheory -> ClsCs -> ClsCs
simplify as theory [] = []
simplify bs theory (ct:cs) = case entail bs theory ct of
  Nothing  -> ct : simplify bs theory cs
  Just cs' -> simplify bs theory (cs' ++ cs)

--something like this:
entail :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> Maybe ([ClsCt], DictSubst)
