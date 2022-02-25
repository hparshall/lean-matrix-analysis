import analysis.inner_product_space.adjoint
import analysis.inner_product_space.pi_L2

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]

variables {T : E →ₗ[𝕜] E} (hsa : inner_product_space.is_self_adjoint T)