import .svd
import data.matrix.basic

variables {n : ℕ} (A : matrix (fin n) (fin n) ℂ)

-- theorem svd_matrix : ∃ U Σ V : matrix (fin n) (fin n) ℂ, A = U * Σ * V ∧ (Uᴴ = U ∧ Vᴴ = V) :=
-- sorry

example : ∃ U : matrix (fin n) (fin n) ℂ, A = U := sorry