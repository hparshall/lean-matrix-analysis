import analysis.inner_product_space.pi_L2
  
variables {ι : Type*} [fintype ι]
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
variables {E' : Type*} [inner_product_space 𝕜 E']

variables {m n : ℕ}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (euclidean_space 𝕜 (fin m)) _ x y

open_locale matrix

lemma inner_matrix_row_row (A : matrix (fin n) (fin m) 𝕜) (i j : (fin n)) :
  ⟪A i, A j⟫ = (A ⬝ Aᴴ) j i := by {simp only [inner, matrix.mul_apply, star_ring_end_apply,
    matrix.conj_transpose_apply,mul_comm]}