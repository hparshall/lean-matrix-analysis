import analysis.inner_product_space.adjoint

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E]

open_locale big_operators matrix topological_space

namespace continuous_linear_map

lemma norm_map_of_unitary {U : (E →L[𝕜] E)} (hU : U ∈ unitary (E →L[𝕜] E)) (x : E) :
  ∥U x∥ = ∥x∥ :=
begin
  rw ← sq_eq_sq (norm_nonneg (U x)) (norm_nonneg x),
  rw [norm_sq_eq_inner, ← continuous_linear_map.adjoint_inner_left,
    ← continuous_linear_map.mul_apply],
  rw unitary.mem_iff at hU,
  rw [← continuous_linear_map.star_eq_adjoint, hU.1, continuous_linear_map.one_apply,
    inner_self_eq_norm_sq],
end

lemma op_norm_of_unitary [nontrivial E] {U : (E →L[𝕜] E)} (hU : U ∈ unitary (E →L[𝕜] E)) :
  ∥U∥ = 1 :=
begin
  have h_above : ∀ (x : E), ∥U x∥ ≤ 1 * ∥x∥,
  { intro x,
    rw norm_map_of_unitary hU,
    norm_num },
  have h_below : ∀ (N : ℝ), N ≥ 0 → (∀ (x : E), ∥U x∥ ≤ N * ∥x∥) → 1 ≤ N,
  { intros N hN_zero,
    contrapose,
    push_neg,
    intro hN_one,
    have hy_nonzero : ∃ (y : E), y ≠ 0 := exists_ne 0,
    cases hy_nonzero with y hy,
    use y,
    rw norm_map_of_unitary hU,
    have hy_pos : 0 < ∥y∥ := by {rw norm_pos_iff, exact hy},
    rw mul_lt_iff_lt_one_left hy_pos,
    exact hN_one },
  apply continuous_linear_map.op_norm_eq_of_bounds zero_le_one h_above h_below,
end

end continuous_linear_map