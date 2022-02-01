import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import linear_algebra.basis

variables {n : ℕ} (S : submodule ℂ (euclidean_space ℂ (fin n)))

variable (L : S →ₗᵢ[ℂ] (euclidean_space ℂ (fin n))) -- errors
/--
failed to synthesize type class instance for
𝕜 : Type u_1,
_inst_1 : is_R_or_C 𝕜,
n : ℕ,
S : submodule 𝕜 (euclidean_space 𝕜 (fin n))
⊢ module 𝕜 (euclidean_space 𝕜 (fin n))
--/