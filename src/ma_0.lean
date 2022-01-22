import analysis.inner_product_space.pi_L2
import linear_algebra.matrix

open_locale big_operators matrix

variables {m n: Type*}
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [has_lt m] [has_lt n]

local notation `Tr` := matrix.trace _ ℂ ℂ

lemma trace_eq_l2 (A : matrix m n ℂ) : Tr (Aᴴ ⬝ A) = ∑ (i : m) (j : n), inner (A i j) (A i j) :=
begin
  rw matrix.trace_apply,
  have fact₁ : (∑ (j : n), (Aᴴ ⬝ A) j j) = (∑ (j : n) (i : m), inner (A i j) (A i j)) := by ring,
  rw fact₁,
  rw finset.sum_comm,
end