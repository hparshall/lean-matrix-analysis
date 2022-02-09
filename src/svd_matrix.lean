import .svd
import data.matrix.basic



-- -- theorem svd_matrix : ∃ U Σ V : matrix (fin n) (fin n) ℂ, A = U * Σ * V ∧ (Uᴴ = U ∧ Vᴴ = V) :=
-- -- sorry

variables {n : ℕ} (A : matrix (fin n) (fin n) ℂ)

open_locale matrix

def matrix_to_lin_end (B : matrix (fin n) (fin n) ℂ) : (ℂ^n) → (ℂ^n) :=
begin
  let T := (id (B.to_lin') : (ℂ^n) → ℂ^n),
  exact T,
end


example : ∃ (U V: matrix (fin n) (fin n) ℂ) (s : (fin n) → ℂ), A = U * (matrix.diagonal s) * Vᴴ ∧ (Uᴴ = U) ∧ (Vᴴ = V) :=
begin
  let T := (id(A.to_lin') : Lℂ^n),
  have svd_T := svd T,
  
end
