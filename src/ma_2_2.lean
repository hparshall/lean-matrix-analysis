import analysis.inner_product_space.pi_L2
import linear_algebra.dimension
import linear_algebra.matrix
import .ma_2_1

open_locale big_operators matrix

variables {m n: Type*}
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [has_lt m] [has_lt n]

def unitarily_similar (A : matrix n n ℂ) (B : matrix n n ℂ) :=
  ∃ U : matrix n n ℂ, (A = U ⬝ B ⬝ Uᴴ) ∧ (is_unitary U)

theorem thm_2_2_2 (U : matrix m m ℂ) (V : matrix n n ℂ) (hu: is_unitary U) (hv : is_unitary V)
  (A : matrix m n ℂ) (B : matrix m n ℂ) (hab : A = U ⬝ B ⬝ V) :
  ∑ (i : m) (j : n), ∥A i j∥^2 = ∑ (i : m) (j : n), ∥B i j∥^2 :=
begin
  sorry
end
