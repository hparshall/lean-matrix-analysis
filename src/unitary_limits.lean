import analysis.inner_product_space.adjoint

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E]

open_locale big_operators matrix topological_space

lemma seq_unitary_tendsto_unitary {A : ℕ → (E →L[𝕜] E)} {L : (E →L[𝕜] E)}
  (hA : ∀ (i : ℕ), A i ∈ unitary (E →L[𝕜] E)) (hL : filter.tendsto A filter.at_top (𝓝 L)) :
  L ∈ unitary (E →L[𝕜] E) :=
begin
  rw unitary.mem_iff,
  have h_star : filter.tendsto (star A) filter.at_top (𝓝 (star L)) :=
    @filter.tendsto.star _ _ _ _ _ A filter.at_top L hL,
  have tendsto_starLL : filter.tendsto ((star A) * A) filter.at_top (𝓝 ((star L) * L)) :=
    @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ h_star hL,
  have tendsto_LstarL : filter.tendsto (A * (star A)) filter.at_top (𝓝 (L * (star L))) :=
    @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ hL h_star,
  have h_starLL : filter.tendsto ((star A) * A) filter.at_top (𝓝 (1)) :=
  begin
    intros s h,
    simp only [filter.mem_at_top_sets, filter.mem_map],
    use 0,
    intros b h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply, unitary.star_mul_self_of_mem],
    apply mem_of_mem_nhds,
    have : star (A b) * (A b) = 1 :=
    begin
      specialize hA b,
      rw unitary.mem_iff at hA,
      exact hA.1,
    end,
    rw this,
    exact h,
  end,
  have h_LstarL : filter.tendsto (A * (star A)) filter.at_top (𝓝 (1)) :=
  begin
    intros s h,
    simp only [filter.mem_at_top_sets, filter.mem_map],
    use 0,
    intros b h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply, unitary.star_mul_self_of_mem],
    apply mem_of_mem_nhds,
    have : (A b) * star (A b) = 1 :=
    begin
      specialize hA b,
      rw unitary.mem_iff at hA,
      exact hA.2,
    end,
    rw this,
    exact h,
  end,
  have lim_LstarL : lim filter.at_top (A * (star A)) = L * (star L) :=
    filter.tendsto.lim_eq tendsto_LstarL,
  have lim_one : lim filter.at_top (A * (star A)) = 1 :=
    filter.tendsto.lim_eq h_LstarL,
  have lim_starLL : lim filter.at_top ((star A) * A) = (star L) * L :=
    filter.tendsto.lim_eq tendsto_starLL,
  have lim_two : lim filter.at_top ((star A) * A) = 1 :=
    filter.tendsto.lim_eq h_starLL,
  rw [← lim_LstarL, ← lim_starLL],
  split,
  exact lim_two,
  exact lim_one,
end
