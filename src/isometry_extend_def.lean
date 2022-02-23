import analysis.inner_product_space.pi_L2

variables {E : Type*}
[inner_product_space ℂ E]
[finite_dimensional ℂ E]

variables {S : submodule ℂ E} {L : S →ₗᵢ[ℂ] E}

open finite_dimensional

/-- Let `S` be a subspace of a finite-dimensional complex inner product space `E`.  A linear
isometry mapping `S` into `E` can be extended to a full isometry of `E`. -/
noncomputable def linear_isometry.extend (L : S →ₗᵢ[ℂ] E): E →ₗᵢ[ℂ] E :=
  begin
    -- Build an isometry from Sᗮ to L(S)ᗮ through euclidean_space
    let d := finrank ℂ Sᗮ,
    have dim_S : finrank ℂ Sᗮ = d := rfl,
    let LS := L.to_linear_map.range,
    have dim_LS_perp : finrank ℂ LSᗮ = d,
    calc  finrank ℂ LSᗮ = finrank ℂ E - finrank ℂ LS : by simp only
        [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
      ...               = finrank ℂ E - finrank ℂ S : by simp only
        [linear_map.finrank_range_of_inj L.injective]
      ...               = finrank ℂ Sᗮ : by simp only
        [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
      ...               = d : dim_S,
    let L1 := ((fin_std_orthonormal_basis dim_S).to_orthonormal_basis
      (fin_std_orthonormal_basis_orthonormal dim_S)).repr.to_linear_isometry,
    let L2 := ((fin_std_orthonormal_basis dim_LS_perp).to_orthonormal_basis
      (fin_std_orthonormal_basis_orthonormal dim_LS_perp)).repr.symm.to_linear_isometry,
    let L3 := (LS)ᗮ.subtypeₗᵢ.comp (L2.comp L1),
    -- Project onto S and Sᗮ
    let p1 := (orthogonal_projection S).to_linear_map,
    let p2 := (orthogonal_projection Sᗮ).to_linear_map,
    -- Build a linear map from the isometries on S and Sᗮ
    let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2,
    -- Prove that M is an isometry
    have M_norm_map : ∀ (x : E), ∥M x∥ = ∥x∥,
    { intro x,
      -- Apply M to the orthogonal decomposition of x
      have Mx_decomp : M x = L (p1 x) + L3 (p2 x),
      { simp only [linear_map.add_apply, linear_map.comp_apply, linear_map.comp_apply,
        linear_isometry.coe_to_linear_map]},
      -- Mx_decomp is the orthogonal decomposition of M x
      have Mx_orth : ⟪ L (p1 x), L3 (p2 x) ⟫_ℂ = 0,
      { have Lp1x : L (p1 x) ∈ L.to_linear_map.range := L.to_linear_map.mem_range_self (p1 x),
        have Lp2x : L3 (p2 x) ∈ (L.to_linear_map.range)ᗮ,
        { simp only [L3, linear_isometry.coe_comp, function.comp_app, submodule.coe_subtypeₗᵢ, 
            ← submodule.range_subtype (LSᗮ)],
          apply linear_map.mem_range_self},
        apply submodule.inner_right_of_mem_orthogonal Lp1x Lp2x},
      -- Apply the Pythagorean theorem and simplify
      rw ← sq_eq_sq (norm_nonneg _) (norm_nonneg _),
      rw norm_sq_eq_add_norm_sq_projection x S,
      simp only [sq, Mx_decomp],
      rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth,
      simp only [linear_isometry.norm_map, p1, p2, continuous_linear_map.to_linear_map_eq_coe,
        add_left_inj, mul_eq_mul_left_iff, norm_eq_zero, true_or, eq_self_iff_true,
        continuous_linear_map.coe_coe, submodule.coe_norm, submodule.coe_eq_zero]},
    exact {
      to_linear_map := M,
      norm_map' := M_norm_map,
    },
  end

lemma linear_isometry.extend_apply (L : S →ₗᵢ[ℂ] E) (s : S):
  L.extend s = L s :=
begin
  simp only [linear_isometry.extend, continuous_linear_map.to_linear_map_eq_coe,
    ←linear_isometry.coe_to_linear_map],
  simp only [add_right_eq_self, linear_isometry.coe_to_linear_map, 
    linear_isometry_equiv.coe_to_linear_isometry, linear_isometry.coe_comp, function.comp_app,
    orthogonal_projection_mem_subspace_eq_self, linear_map.coe_comp, continuous_linear_map.coe_coe,
    submodule.coe_subtype, linear_map.add_apply, submodule.coe_eq_zero, 
    linear_isometry_equiv.map_eq_zero_iff, submodule.coe_subtypeₗᵢ,
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
    submodule.orthogonal_orthogonal, submodule.coe_mem],
end