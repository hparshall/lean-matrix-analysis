import analysis.inner_product_space.pi_L2
import linear_algebra.dimension
import linear_algebra.matrix
import data.matrix.basic
import .ma_2_1

open_locale big_operators matrix

variables {m n: Type*}
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [has_lt m] [has_lt n]

variables (A B : matrix n n ℂ)

def unitarily_similar :=
  ∃ U : matrix n n ℂ, (A = U ⬝ B ⬝ Uᴴ) ∧ is_unitary U

def equality (a : ℕ) (b : ℕ) := a = b

def matrix_equal := A = B

example : @equivalence (matrix n n ℂ) unitarily_similar:=

begin
  split,
  rw reflexive,
  intro x,
  use 1,
  split,
  simp,
  rw is_unitary,
  simp,
  split,
  intros a b h,
  cases h with U hU,
  use Uᴴ,
  cases hU with hU1 hU2,
  rw is_unitary at hU2,
  split,
  apply symm,
  calc Uᴴ ⬝ a ⬝ Uᴴᴴ = Uᴴ ⬝ a ⬝ U : by {simp}
  ...               = Uᴴ ⬝ U ⬝ b ⬝ Uᴴ ⬝ U : by {rw hU1, rw ← matrix.mul_assoc, rw ← matrix.mul_assoc}
  ...               = b : by {rw hU2, rw matrix.mul_assoc, rw hU2, simp},

  exact (thm_2_1_4_a_d U).1 hU2,

  intros A B C hAB hBC,
  cases hAB with U hU,
  cases hBC with V hV,
  use (U ⬝ V),
  split,
  calc A = U ⬝ B ⬝ Uᴴ :  hU.1
  ...    = U ⬝ V ⬝ C ⬝ Vᴴ ⬝ Uᴴ : by {rw hV.1, rw ← matrix.mul_assoc, rw ← matrix.mul_assoc}
  ...    = U ⬝ V ⬝ C ⬝ (U ⬝ V)ᴴ : by {simp, rw matrix.mul_assoc},
  rw is_unitary,
  rw is_unitary at hU,
  rw is_unitary at hV,
  calc (U ⬝ V)ᴴ ⬝ (U ⬝ V) = Vᴴ ⬝ (Uᴴ ⬝ U) ⬝ V : by {simp, rw ← matrix.mul_assoc, rw ← matrix.mul_assoc}
  ...                     = Vᴴ ⬝ V : by {rw hU.2, simp}
  ...                     = 1 : by {rw hV.2},
end

def fro (A : matrix n n ℂ) : ℝ := ∑ (i : n) (j : n), complex.norm_sq(A i j )

theorem thm_2_2_2 (U V : matrix n n ℂ) [is_unitary U] [is_unitary V] : (A = U ⬝ B ⬝ V) → fro A = fro B :=
begin
  sorry
end
