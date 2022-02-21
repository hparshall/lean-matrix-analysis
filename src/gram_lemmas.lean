import analysis.inner_product_space.adjoint

variables {E 𝕜 : Type*}
[is_R_or_C 𝕜]
[inner_product_space 𝕜 E]
[finite_dimensional 𝕜 E]

namespace inner_product_space

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

lemma gram_self_adjoint (T : E →ₗ[𝕜] E): is_self_adjoint (T.adjoint * T) :=
begin
  intros x y,
  simp only [linear_map.mul_apply, linear_map.adjoint_inner_left, linear_map.adjoint_inner_right],
end

lemma gram_positive (T : E →ₗ[𝕜] E) :
∀ (x : E), is_R_or_C.re ⟪ (T.adjoint * T) x, x ⟫ ≥ 0 ∧ is_R_or_C.im ⟪ (T.adjoint * T) x, x⟫ = 0 :=
begin
  intro x,
  rw [linear_map.mul_apply, linear_map.adjoint_inner_left, inner_self_eq_norm_sq_to_K],
  norm_cast,
  split,
  {apply sq_nonneg _},
  {refl},
end

end inner_product_space