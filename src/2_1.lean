import analysis.inner_product_space.pi_L2
import linear_algebra.matrix
import linear_algebra.unitary_group

open_locale matrix

variables {F m n: Type*}
  [is_R_or_C F]
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]

theorem thm_2_1_2 (v : n → (euclidean_space F m)) (hon : (orthonormal F v)) :
linear_independent F v := orthonormal.linear_independent hon

def is_unitary (A : matrix n n F) := Aᴴ ⬝ A = 1

def is_orthogonal (A : matrix n n ℝ) := Aᵀ ⬝ A = 1

lemma eq_0_5 (A : matrix n n F) (B : matrix n n F) : B ⬝ A = 1 ↔ A ⬝ B = 1 :=
begin
  apply matrix.mul_eq_one_comm,
end

theorem thm_2_1_4_a_b (A : matrix n n F) : (is_unitary A) ↔ (is_unit A) ∧ (A⁻¹ = Aᴴ) :=
begin
  split,
  intro h,
  split,
  rw is_unit,
  use A,
  exact Aᴴ,
  simp,
  rw eq_0_5,
  exact h,
  exact h,
  simp,
  apply matrix.inv_eq_left_inv _,
  exact h,
  intro h,
  cases h with h1 h2,
  rw is_unitary,
  rw ← h2,
  rw matrix.is_unit_iff_is_unit_det at h1,
  apply matrix.nonsing_inv_mul A h1,
end

theorem thm_2_1_4_b_c (A : matrix n n F) : ( (is_unit A) ∧ (A⁻¹ = Aᴴ) ) ↔ A ⬝ Aᴴ = 1 :=
begin
  split,
  intro h,
  rw eq_0_5,
  cases h with h1 h2,
  rw ← h2,
  rw matrix.is_unit_iff_is_unit_det at h1,
  apply matrix.nonsing_inv_mul A h1,
  intro h,
  split,
  rw is_unit,
  use A,
  use Aᴴ,
  simp,
  exact h,
  simp,
  rw eq_0_5,
  exact h,
  simp,
  apply matrix.inv_eq_right_inv h,
end

theorem thm_2_1_4_c_d (A : matrix n n F) : (A ⬝ Aᴴ = 1) ↔ is_unitary Aᴴ :=
begin
  split,
  intro h,
  rw is_unitary,
  simp,
  exact h,
  rw is_unitary,
  simp,
end