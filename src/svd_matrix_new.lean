import .gram_sqrt
import .polar_decomp
import data.matrix.basic
import algebra.star.basic


variables {n : ℕ} (A : matrix (fin n) (fin n) ℂ)

open_locale matrix

def svd_matrix_left (A : matrix (fin n) (fin n) ℂ) : matrix (fin n) (fin n) ℂ :=
begin
  
end


def svd_matrix_diag (A : matrix (fin n) (fin n) ℂ) : matrix (fin n) (fin n) ℂ := sorry

def svd_matrix_right (A : matrix (fin n) (fin n) ℂ) : matrix (fin n) (fin n) ℂ := sorry


theorem svd_matrix (A : matrix (fin n) (fin n) ℂ) : A = svd_matrix_left A ⬝ (svd_matrix_diag A) ⬝ (svd_matrix_right A) :=
begin

end