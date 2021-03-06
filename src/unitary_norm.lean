import analysis.inner_product_space.adjoint

variables {š E : Type*} [is_R_or_C š] [inner_product_space š E] [complete_space E]

open_locale big_operators matrix topological_space

namespace continuous_linear_map

lemma norm_map_of_unitary {U : (E āL[š] E)} (hU : U ā unitary (E āL[š] E)) (x : E) :
  ā„U xā„ = ā„xā„ :=
begin
  rw ā sq_eq_sq (norm_nonneg (U x)) (norm_nonneg x),
  rw [norm_sq_eq_inner, ā continuous_linear_map.adjoint_inner_left,
    ā continuous_linear_map.mul_apply],
  rw unitary.mem_iff at hU,
  rw [ā continuous_linear_map.star_eq_adjoint, hU.1, continuous_linear_map.one_apply,
    inner_self_eq_norm_sq],
end

lemma op_norm_of_unitary [nontrivial E] {U : (E āL[š] E)} (hU : U ā unitary (E āL[š] E)) :
  ā„Uā„ = 1 :=
begin
  have h_above : ā (x : E), ā„U xā„ ā¤ 1 * ā„xā„,
  { intro x,
    rw norm_map_of_unitary hU,
    norm_num },
  have h_below : ā (N : ā), N ā„ 0 ā (ā (x : E), ā„U xā„ ā¤ N * ā„xā„) ā 1 ā¤ N,
  { intros N hN_zero,
    contrapose,
    push_neg,
    intro hN_one,
    have hy_nonzero : ā (y : E), y ā  0 := exists_ne 0,
    cases hy_nonzero with y hy,
    use y,
    rw norm_map_of_unitary hU,
    have hy_pos : 0 < ā„yā„ := by {rw norm_pos_iff, exact hy},
    rw mul_lt_iff_lt_one_left hy_pos,
    exact hN_one },
  apply continuous_linear_map.op_norm_eq_of_bounds zero_le_one h_above h_below,
end

end continuous_linear_map