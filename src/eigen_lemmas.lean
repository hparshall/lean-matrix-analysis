import analysis.inner_product_space.spectrum

variables {ð : Type*} [is_R_or_C ð] [decidable_eq ð] 
variables {E : Type*} [inner_product_space ð E] [finite_dimensional ð E]
variables {T : E ââ[ð] E}

local notation `âŠ`x`, `y`âŦ` := @inner ð E _ x y

namespace inner_product_space

lemma is_self_adjoint.pos_nonneg_eigenvalues {n : â} (hn : finite_dimensional.finrank ð E = n)
  (hsa : is_self_adjoint T)
  (hpos : â (x : E), (is_R_or_C.re âŠT x, xâŦ âĨ 0)) :
  â (i : (fin n)), hsa.eigenvalues hn i âĨ 0 :=
begin
  intro i,
  have : hsa.eigenvalues hn i = 
    is_R_or_C.re âŠ T (hsa.eigenvector_basis hn i), hsa.eigenvector_basis hn i âŦ :=
  begin
    simp only [inner_smul_left, inner_product_space.is_self_adjoint.apply_eigenvector_basis,
      is_R_or_C.conj_of_real, is_R_or_C.mul_re, is_R_or_C.of_real_re, sub_zero, mul_zero,
      inner_self_nonneg_im, is_R_or_C.of_real_im, inner_self_eq_norm_sq_to_K],
    rw (hsa.eigenvector_basis_orthonormal hn).1,
    norm_num,
  end,
  rw this,
  exact (hpos (hsa.eigenvector_basis hn i)),
end

end inner_product_space