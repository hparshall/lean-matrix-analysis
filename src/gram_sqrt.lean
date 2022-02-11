import .square_root
/-
uses is_positive, thm_7_35_b_c
-/

-- Checked over by:
-- Dan

/-
The goal of this file is to show that (T† T), the Gram operator of T, has a square root:
-/


variables {n : ℕ} (T : Lℂ^n)

open_locale big_operators complex_conjugate matrix

localized "postfix `†`:1000 := linear_map.adjoint" in src


/-
The Gram operator is self-adjoint
-/
lemma gram_sa :
  inner_product_space.is_self_adjoint (T† * T) :=
begin
  intros x y,
  rw [← linear_map.adjoint_inner_right, mul_adjoint, linear_map.adjoint_adjoint],
end

/-
The Gram operator is positive
-/
lemma gram_pos :
  is_positive (T† * T) :=
begin
  intro x,
  rw [linear_map.mul_apply, linear_map.adjoint_inner_left, inner_self_eq_norm_sq_to_K],
  norm_cast,
  exact ⟨ sq_nonneg (∥ T x ∥), rfl ⟩,
end

/-
The Gram operator has a square root
-/
lemma sqrt_gram_exists :
  ∃ (R : Lℂ^n), (R^2 = T† * T) ∧ (inner_product_space.is_self_adjoint R) ∧ (is_positive R) := 
    sqrt_exists (T† * T) (gram_sa _) (gram_pos _)