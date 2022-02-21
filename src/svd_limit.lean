import data.complex.is_R_or_C
import analysis.inner_product_space.pi_L2

variables {m n : ℕ}

variables (𝕜 : Type*)
[is_R_or_C 𝕜]

open_locale big_operators complex_conjugate matrix topological_space

local notation `𝕜^n` := (euclidean_space 𝕜 (fin n))

local notation `M_n` := (matrix (fin n) (fin n) 𝕜)

local notation `U_n` := matrix.unitary_group (fin n) 𝕜

variables (A B : ℕ → M_n) (L : M_n)


/-
matrix_SVD should look like this:
-/
noncomputable def matrix_SVD (M : M_n) : (fin 3) → M_n := sorry


theorem limit_svd_is_svd (h_lim : filter.tendsto A filter.at_top (𝓝 L))