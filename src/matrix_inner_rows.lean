import analysis.inner_product_space.pi_L2
  
variables {Ī¹ : Type*} [fintype Ī¹]
variables {š : Type*} [is_R_or_C š] {E : Type*} [inner_product_space š E]
variables {E' : Type*} [inner_product_space š E']

variables {m n : ā}

local notation `āŖ`x`, `y`ā«` := @inner š (euclidean_space š (fin m)) _ x y

open_locale matrix

lemma inner_matrix_row_row (A : matrix (fin n) (fin m) š) (i j : (fin n)) :
  āŖA i, A jā« = (A ā¬ Aį““) j i := by {simp only [inner, matrix.mul_apply, star_ring_end_apply,
    matrix.conj_transpose_apply,mul_comm]}