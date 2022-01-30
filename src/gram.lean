import .ladr_7_35

variables {n : ℕ} (T : Lℂ^n)

open_locale big_operators complex_conjugate matrix

lemma gram_sa :
  is_sa (T.adjoint * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

lemma gram_pos :
  is_positive (T.adjoint * T) :=
begin
  rw is_positive,
  intro x,
  have h1 : ⟪ (T.adjoint * T) x, x ⟫_ℂ = ⟪ (linear_map.adjoint T) (T x), x ⟫_ℂ :=
  begin
    rw linear_map.mul_apply,
  end,
  rw h1,
  rw linear_map.adjoint_inner_left,
  rw ← is_R_or_C.re_to_complex,
  rw ← is_R_or_C.im_to_complex,
  rw inner_self_eq_norm_sq,
  norm_cast,
  split,
  exact sq_nonneg (∥ T x ∥),
  rw inner_self_nonneg_im,
end

lemma sqrt_gram :
  ∃ (R : Lℂ^n), (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  have hg : is_sa (T.adjoint * T) := by exact gram_sa T,
  apply thm_7_35_b_c,
  apply gram_pos,
  apply thm_7_35_a_b,
  apply gram_pos,
  exact hg,
end