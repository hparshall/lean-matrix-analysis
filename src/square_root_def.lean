import analysis.inner_product_space.adjoint
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum

variables {ð E : Type*} [is_R_or_C ð] [inner_product_space ð E] [finite_dimensional ð E]
  [decidable_eq ð] 

local notation `âª`x`, `y`â«` := @inner ð E _ x y

namespace inner_product_space

variables {T : E ââ[ð] E} (hT : is_self_adjoint T) 
variables {n : â} (hn : finite_dimensional.finrank ð E = n)

noncomputable def is_self_adjoint.sqrt : E ââ[ð] E :=
  @basis.constr (fin n) ð E E _ _ _ _ _ (hT.eigenvector_basis hn) ð _ _ _
    (Î» (i : (fin n)), (real.sqrt(hT.eigenvalues hn i) : ð) â¢ (hT.eigenvector_basis hn i))

local notation `evec` := hT.eigenvector_basis hn
local notation `eval` := hT.eigenvalues hn

lemma is_self_adjoint.sqrt_apply {i : (fin n)} :
  (hT.sqrt hn) (evec i) = (real.sqrt (eval i) : ð) â¢ (evec i) :=
    by simp only [is_self_adjoint.sqrt, (evec).constr_basis]

lemma is_self_adjoint.sqrt_mul_self_eq (hnn : â (i : (fin n)), eval i â¥ 0) :
  (hT.sqrt hn) * (hT.sqrt hn) = T :=
begin
  apply basis.ext (hT.eigenvector_basis hn),
  intro i,
  simp only [linear_map.mul_apply, inner_product_space.is_self_adjoint.apply_eigenvector_basis,
    is_self_adjoint.sqrt_apply, ring_hom.id_apply, linear_map.map_smulââ, smul_smul],
  norm_cast,
  rw real.mul_self_sqrt (hnn i),
end

lemma is_self_adjoint.sqrt_self_adjoint : is_self_adjoint (hT.sqrt hn) :=
begin
  rw [linear_map.is_self_adjoint_iff_eq_adjoint, linear_map.eq_adjoint_iff_basis (evec) (evec)],
  intros i j,
  simp only [is_self_adjoint.sqrt_apply, inner_smul_left, inner_smul_right, is_R_or_C.conj_of_real,
    is_R_or_C.of_real_inj, mul_eq_mul_right_iff],
  by_cases hij : i = j,
  simp only [hij, true_or, eq_self_iff_true, inner_self_eq_zero],
  have orthonormal_evec : orthonormal ð evec := is_self_adjoint.eigenvector_basis_orthonormal hT hn,
  rw orthonormal_iff_ite at orthonormal_evec,
  specialize orthonormal_evec i j,
  simp only [orthonormal_evec, ite_eq_right_iff],
  tauto,
end

end inner_product_space