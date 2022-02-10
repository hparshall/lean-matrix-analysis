import .ladr_7_35
/-
uses is_positive, thm_7_35_b_c
-/


variables {n : ℕ} (T : Lℂ^n)

open_locale big_operators complex_conjugate matrix

localized "postfix `†`:1000 := linear_map.adjoint" in src

lemma gram_sa :
  inner_product_space.is_self_adjoint (T† * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

lemma gram_pos :
  is_positive (T† * T) :=
begin
  rw is_positive,
  intro x,
  have h1 : ⟪ (T† * T) x, x ⟫_ℂ = ⟪ (T†) (T x), x ⟫_ℂ := by rw linear_map.mul_apply,
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
  ∃ (R : Lℂ^n), (R^2 = T† * T) ∧ (inner_product_space.is_self_adjoint R) ∧ (is_positive R) :=
begin
  have hg : inner_product_space.is_self_adjoint (T† * T) := by exact gram_sa T,
  apply thm_7_35_b_c,
  exact hg,
  apply gram_pos,
end