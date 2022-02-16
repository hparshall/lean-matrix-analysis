import analysis.inner_product_space.basic

variables {E : Type*}
[inner_product_space ℂ E]

/--
A complex polarization identity, with a linear map
-/
lemma inner_map_polarization (T : E →ₗ[ℂ] E) (x y : E):
  ⟪ T y, x ⟫_ℂ = (⟪T (x + y) , x + y⟫_ℂ - ⟪T (x - y) , x - y⟫_ℂ + complex.I * ⟪T (x + complex.I • y) , x + complex.I • y⟫_ℂ - complex.I * ⟪T (x - complex.I • y), x - complex.I • y ⟫_ℂ) / 4 :=
begin
  iterate {rw [map_add, inner_add_left, inner_add_right, inner_add_right]},
  iterate {rw [map_sub,inner_sub_left, inner_sub_right, inner_sub_right]},
  rw [linear_map.map_smul, inner_smul_left, inner_smul_right],
  ring_nf,
  rw complex.conj_I,
  ring_nf,
  rw complex.I_sq,
  ring_nf,
end

/--
If `⟪T x, x⟫_ℂ = 0` for all x, then T = 0.
-/
lemma inner_map_self_eq_zero (T : E →ₗ[ℂ] E) (hT : ∀ (x : E), ⟪T x, x⟫_ℂ = 0) :
  T = 0 :=
begin
  apply linear_map.ext,
  intro x,
  rw [linear_map.zero_apply, ← inner_self_eq_zero, inner_map_polarization],
  iterate {rw hT},
  norm_num,
end