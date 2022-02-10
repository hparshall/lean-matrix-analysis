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

lemma basis_to_matrix_to_lin (b₁ b₂: basis (fin n) ℂ ℂ^n) (v : ℂ^n) : matrix.to_lin' ((b₁.to_matrix b₂)ᴴ) v = ∑ (i : (fin n)), ⟪ b₂ i, v ⟫_ℂ • (b₁ i) :=
begin
  rw matrix.to_lin'_apply,

end


-- TODO:  Define singular values for matrices 

example : ∃ (U V : matrix (fin n) (fin n) ℂ) (s : (fin n) → ℝ), A = U * (matrix.diagonal ↑s) * Vᴴ ∧ (Uᴴ ⬝ U = 1) ∧ (Vᴴ ⬝ V = 1) :=
begin
  let T := (id(A.to_lin') : Lℂ^n),
  choose e f svd_T using (svd T),
  let std_basis : basis (fin n) ℂ ℂ^n := pi.basis_fun ℂ (fin n),
  let U := std_basis.to_matrix ⇑f,
  let V := std_basis.to_matrix ⇑e,
  use U,
  use V,
  use (singular_values T),
  split,
  simp only [U, V],
  simp only [matrix.mul_eq_mul],
  rw matrix_eq_iff_lin_eq,
  ext1,
  rw svd_T.2 x,

end
