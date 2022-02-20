import analysis.inner_product_space.spectrum

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] 
variables {E : Type*} [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
variables {T : E →ₗ[𝕜] E}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

namespace inner_product_space

lemma is_self_adjoint.pos_nonneg_eigenvalues {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)
  (hsa : is_self_adjoint T)
  (hpos : ∀ (x : E), (is_R_or_C.re ⟪T x, x⟫ ≥ 0)) :
  ∀ (i : (fin n)), hsa.eigenvalues hn i ≥ 0 :=
begin
  intro i,
  have : hsa.eigenvalues hn i = 
    is_R_or_C.re ⟪ T (hsa.eigenvector_basis hn i), hsa.eigenvector_basis hn i ⟫ :=
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