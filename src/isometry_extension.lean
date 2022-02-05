import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.inner_product_space.l2_space
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem
import .linear_independent

variable {n : ℕ}
variable T : Lℂ^n
-- Dan's work on trying to extend isometries
example (M : submodule ℂ ℂ^n) (S₀ : M →ₗᵢ[ℂ] M) : ∃ S : (ℂ^n) →ₗᵢ[ℂ] ℂ^n, orthogonal_projection M ∘ (linear_map.dom_restrict S.to_linear_map M) = S₀ :=
begin
  have exists_w := exists_hilbert_basis ℂ M,
  let w'' := classical.some exists_w,
  let b₀ : hilbert_basis w'' ℂ M := classical.some (classical.some_spec exists_w),

  let w' : set (ℂ^n) := sorry,
  let b' : w' → (ℂ^n) := coe,
  have : orthonormal ℂ (coe : w' → ℂ^n) := sorry,
  have : ∃ (w : set ℂ^n) (b : hilbert_basis w ℂ ℂ^n), w' ⊆ w ∧ ⇑b = (coe : w → ℂ^n) := orthonormal.exists_hilbert_basis_extension this,

end

#check T.range_restrict