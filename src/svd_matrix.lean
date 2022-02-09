import .svd
import data.matrix.basic



-- -- theorem svd_matrix : ∃ U Σ V : matrix (fin n) (fin n) ℂ, A = U * Σ * V ∧ (Uᴴ = U ∧ Vᴴ = V) :=
-- -- sorry

variables {n : ℕ} (A : matrix (fin n) (fin n) ℂ)

open_locale matrix big_operators
open classical

def matrix_to_lin_end (B : matrix (fin n) (fin n) ℂ) : (ℂ^n) → (ℂ^n) :=
begin
  let T := (id (B.to_lin') : (ℂ^n) → ℂ^n),
  exact T,
end

def matrix_eq_iff_lin_eq (A B : matrix (fin n) (fin n) ℂ) : A = B ↔ (id (A.to_lin') : Lℂ^n) = B.to_lin' :=
begin
  split,
  intro hₘ,
  rw hₘ,
  rw id.def,
  intro h,
  ext1,
  have key : ∀ D : (matrix (fin n) (fin n) ℂ), ((id (matrix.to_lin' D) : Lℂ^n ) (pi.basis_fun ℂ (fin n) j)) i = D i j :=
  begin
    intro D,
    simp only [pi.basis_fun_apply, id.def, matrix.mul_vec_std_basis, matrix.to_lin'_apply],
  end,
  rw ← key A,
  rw ← key B,
  rw h,
  rw id.def,
end


example : ∃ (U V: matrix (fin n) (fin n) ℂ) (s : (fin n) → ℝ), A = U * (matrix.diagonal ↑s) * Vᴴ ∧ (Uᴴ ⬝ U = 1) ∧ (Vᴴ ⬝ V = 1) :=
begin
  let T := (id(A.to_lin') : Lℂ^n),
  have svd_T := svd T,
  let e := some svd_T,
  have svd_T' : ∃ f : (basis (fin n) ℂ ℂ^n), (orthonormal ℂ e ∧ orthonormal ℂ f) ∧ ∀ v : ℂ^n, T v = ∑ (i : (fin n)), singular_values T i • ⟪e i, v ⟫_ℂ • (f i) := some_spec svd_T,
  let f := some svd_T',
  have svd_T'' : (orthonormal ℂ e ∧ orthonormal ℂ f) ∧ ∀ v : ℂ^n, T v = ∑ (i : (fin n)), singular_values T i • ⟪e i, v ⟫_ℂ • (f i) := some_spec svd_T',
  let std_basis : basis (fin n) ℂ ℂ^n := pi.basis_fun ℂ (fin n),
  let U := std_basis.to_matrix ⇑f,
  let V := std_basis.to_matrix ⇑e,
  use U,
  use V,
  use (singular_values T),
  split,
  rw matrix_eq_iff_lin_eq,
  ext1,
  rw svd_T''.2 x,
  simp only [U, V],
  sorry,
end
