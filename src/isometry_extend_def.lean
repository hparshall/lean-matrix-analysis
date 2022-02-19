import analysis.inner_product_space.projection
import analysis.inner_product_space.pi_L2

variables {E : Type*}
[inner_product_space ℂ E]
[finite_dimensional ℂ E]

variables {S : submodule ℂ E} {L : S →ₗᵢ[ℂ] E}

open finite_dimensional

lemma finrank_range_of_inj (hL : function.injective L) :
  (finrank ℂ L.to_linear_map.range) = (finrank ℂ S) :=
begin
  sorry,
end

lemma finrank_orthogonal_range_of_inj (hL: function.injective L) :
  (finrank ℂ (L.to_linear_map.range)ᗮ) = (finrank ℂ Sᗮ) :=
begin
  have : (finrank ℂ (L.to_linear_map.range)ᗮ) = (finrank ℂ E) - (finrank ℂ (L.to_linear_map.range)) :=
    by simp only [← (L.to_linear_map.range).finrank_add_finrank_orthogonal, add_tsub_cancel_left, eq_self_iff_true],
  rw this,
  have : (finrank ℂ Sᗮ) = (finrank ℂ E) - (finrank ℂ S) :=
    by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left, eq_self_iff_true],
  rw this,
  have : (finrank ℂ (L.to_linear_map.range)) = (finrank ℂ S) :=
    finrank_range_of_inj hL,
  rw this,
end

lemma norm_sq_eq_norm_sq_projection (x : E) (S : submodule ℂ E) :
  ∥ x ∥^2 = ∥ (orthogonal_projection S) x ∥^2 + ∥ (orthogonal_projection Sᗮ) x ∥^2 :=
begin
  let p1 := (orthogonal_projection S),
  let p2 := (orthogonal_projection Sᗮ),
  have x_decomp : x = (p1 x : E) + (p2 x) :=  
    eq_sum_orthogonal_projection_self_orthogonal_complement S x,    
  have x_orth : ⟪ (p1 x : E), p2 x ⟫_ℂ = 0 :=
  begin
    have p1x : ↑(p1 x) ∈ S := set_like.coe_mem (p1 x),
    have p2x : ↑(p2 x) ∈ Sᗮ := set_like.coe_mem (p2 x),
    apply submodule.inner_right_of_mem_orthogonal p1x p2x,
  end,
  conv
  begin
    to_lhs,
    rw x_decomp,
  end,
  simp only [sq],
  rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((p1 x) : E) (p2 x) x_orth,
  simp only [add_left_inj, mul_eq_mul_left_iff, norm_eq_zero, true_or, eq_self_iff_true,
    submodule.coe_norm, submodule.coe_eq_zero],
end

namespace linear_isometry

noncomputable def extend (L : S →ₗᵢ[ℂ] E): E →ₗᵢ[ℂ] E :=
  {
    to_linear_map :=
    begin
      -- Project onto S and Sᗮ
      let p1 := (orthogonal_projection S).to_linear_map,
      let p2 := (orthogonal_projection Sᗮ).to_linear_map,
      -- Build an isometry from Sᗮ to L(S)ᗮ through euclidean_space
      let L1 := (linear_isometry_equiv.of_inner_product_space
        (@rfl _ (finrank ℂ Sᗮ))).to_linear_isometry,
      let L2 := (linear_isometry_equiv.of_inner_product_space
        (finrank_orthogonal_range_of_inj L.injective)).symm.to_linear_isometry,
      let L3 := (L.to_linear_map.range)ᗮ.subtypeₗᵢ.comp (L2.comp L1),
      -- Build a linear map from the isometries on S and Sᗮ
      let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2,
      exact M,
    end,
    norm_map' :=
    begin
      simp only [],
      -- Same notation as above
      let p1 := (orthogonal_projection S).to_linear_map,
      let p2 := (orthogonal_projection Sᗮ).to_linear_map,
      let L1 := (linear_isometry_equiv.of_inner_product_space
        (@rfl _ (finrank ℂ Sᗮ))).to_linear_isometry,
      let L2 := (linear_isometry_equiv.of_inner_product_space
        (finrank_orthogonal_range_of_inj L.injective)).symm.to_linear_isometry,
      let L3 := (L.to_linear_map.range)ᗮ.subtypeₗᵢ.comp (L2.comp L1),
      let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2,
      intro x,
      -- Apply M to the orthogonal decomposition of x
      have Mx_decomp : M x = L (p1 x) + L3 (p2 x) :=
      begin
        simp only [linear_map.add_apply],
        rw [linear_map.comp_apply, linear_map.comp_apply],
        simp only [linear_isometry.coe_to_linear_map],
      end,
      -- Mx_decomp is the orthogonal decomposition of M x
      have Mx_orth : ⟪ L (p1 x), L3 (p2 x) ⟫_ℂ = 0 :=
      begin
        have Lp1x : L (p1 x) ∈ L.to_linear_map.range := L.to_linear_map.mem_range_self (p1 x),
        have Lp2x : L3 (p2 x) ∈ (L.to_linear_map.range)ᗮ :=
        begin
          simp only [L3, linear_isometry.coe_comp, function.comp_app, submodule.coe_subtypeₗᵢ],
          have : (L.to_linear_map.range)ᗮ = (L.to_linear_map.range)ᗮ.subtype.range :=
            by simp only [submodule.range_subtype, eq_self_iff_true],
          conv
          begin
            congr,
            skip,
            rw this,
          end,
          apply linear_map.mem_range_self,
        end,
        apply submodule.inner_right_of_mem_orthogonal Lp1x Lp2x,
      end,
      rw ← sq_eq_sq,
      -- Apply the Pythagorean theorem and simplify
      rw norm_sq_eq_norm_sq_projection x S,
      simp only [sq, Mx_decomp],
      rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth,
      simp only [linear_isometry.norm_map, p1, p2, continuous_linear_map.to_linear_map_eq_coe,
        add_left_inj, mul_eq_mul_left_iff, norm_eq_zero, true_or, eq_self_iff_true,
        continuous_linear_map.coe_coe, submodule.coe_norm, submodule.coe_eq_zero],
      exact norm_nonneg _,
      exact norm_nonneg x,
    end
  }

lemma extend_extends (L : S →ₗᵢ[ℂ] E) (s : S):
  extend L s = L s :=
begin
  rw extend,
  push_cast,
  simp only [continuous_linear_map.to_linear_map_eq_coe],
  rw ← linear_isometry.coe_to_linear_map,
  simp only [add_right_eq_self, linear_isometry.coe_to_linear_map, 
    linear_isometry_equiv.coe_to_linear_isometry, linear_isometry.coe_comp, function.comp_app,
    orthogonal_projection_mem_subspace_eq_self, linear_map.coe_comp, continuous_linear_map.coe_coe,
    submodule.coe_subtype, linear_map.add_apply, submodule.coe_eq_zero, 
    linear_isometry_equiv.map_eq_zero_iff, submodule.coe_subtypeₗᵢ],
  rw orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
  simp only [submodule.orthogonal_orthogonal, submodule.coe_mem],
end

end linear_isometry