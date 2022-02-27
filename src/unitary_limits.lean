import analysis.inner_product_space.adjoint

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E]

open_locale big_operators matrix topological_space

lemma seq_unitary_tendsto_unitary {U : ℕ → (E →L[𝕜] E)} {L : (E →L[𝕜] E)}
  (hU : ∀ (i : ℕ), U i ∈ unitary (E →L[𝕜] E)) (hL : filter.tendsto U filter.at_top (𝓝 L)) :
  L ∈ unitary (E →L[𝕜] E) :=
begin
  rw unitary.mem_iff,
  have h_star : filter.tendsto (star U) filter.at_top (𝓝 (star L)) :=
    @filter.tendsto.star _ _ _ _ _ U filter.at_top L hL,
  have tendsto_starLL : filter.tendsto ((star U) * U) filter.at_top (𝓝 ((star L) * L)) :=
    @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ h_star hL,
  have tendsto_LstarL : filter.tendsto (U * (star U)) filter.at_top (𝓝 (L * (star L))) :=
    @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ hL h_star,
  have h_starLL : filter.tendsto ((star U) * U) filter.at_top (𝓝 (1)) :=
  begin
    intros s h,
    simp only [filter.mem_at_top_sets, filter.mem_map],
    use 0,
    intros b h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply, unitary.star_mul_self_of_mem],
    apply mem_of_mem_nhds,
    have : star (U b) * (U b) = 1 :=
    begin
      specialize hU b,
      rw unitary.mem_iff at hU,
      exact hU.1,
    end,
    rw this,
    exact h,
  end,
  have h_LstarL : filter.tendsto (U * (star U)) filter.at_top (𝓝 (1)) :=
  begin
    intros s h,
    simp only [filter.mem_at_top_sets, filter.mem_map],
    use 0,
    intros b h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply, unitary.star_mul_self_of_mem],
    apply mem_of_mem_nhds,
    have : (U b) * star (U b) = 1 :=
    begin
      specialize hU b,
      rw unitary.mem_iff at hU,
      exact hU.2,
    end,
    rw this,
    exact h,
  end,
  have lim_LstarL : lim filter.at_top (U * (star U)) = L * (star L) :=
    filter.tendsto.lim_eq tendsto_LstarL,
  have lim_starLL : lim filter.at_top ((star U) * U) = (star L) * L :=
    filter.tendsto.lim_eq tendsto_starLL,
  have lim_one : lim filter.at_top (U * (star U)) = 1 := filter.tendsto.lim_eq h_LstarL,
  have lim_two : lim filter.at_top ((star U) * U) = 1 := filter.tendsto.lim_eq h_starLL,
  rw [← lim_LstarL, ← lim_starLL],
  split,
  exact lim_two,
  exact lim_one,
end
