/-
The goal of this file is to prove the following.  If S ⊆ ℂ^n is a subspace and L : S → V is
an isometry, then there exists an isometry M : ℂ^n → ℂ^n such that M(s) = L(s) for every s ∈ S.

-- Checked over by: 
-- Hans
-/

import analysis.inner_product_space.pi_L2
open_locale complex_conjugate

variable {n : ℕ}

local notation `ℂ^` n := euclidean_space ℂ (fin n)

variables {S : submodule ℂ (ℂ^n)} {L : S →ₗᵢ[ℂ] ℂ^n}

open finite_dimensional
/-
dim L(S) = dim S
-/
lemma finrank_range_of_inj (hL : function.injective L) :
  (finrank ℂ L.to_linear_map.range) = (finrank ℂ S) :=
begin
  sorry,
end


/-
dim L(S)ᗮ = dim Sᗮ
-/
lemma finrank_orthogonal_range_of_inj (hL: function.injective L) :
  (finrank ℂ (L.to_linear_map.range)ᗮ) = (finrank ℂ Sᗮ) :=
begin
  have : (finrank ℂ (L.to_linear_map.range)ᗮ) = (finrank ℂ ℂ^n) - (finrank ℂ (L.to_linear_map.range)) :=
    by simp only [← (L.to_linear_map.range).finrank_add_finrank_orthogonal, add_tsub_cancel_left, eq_self_iff_true],
  rw this,
  have : (finrank ℂ Sᗮ) = (finrank ℂ ℂ^n) - (finrank ℂ S) :=
    by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left, eq_self_iff_true],
  rw this,
  have : (finrank ℂ (L.to_linear_map.range)) = (finrank ℂ S) :=
  begin
    rw finrank_range_of_inj hL,
  end,
  rw this,
end

lemma norm_sq_eq_norm_sq_proj_orthogonal (x : ℂ^n) (S : submodule ℂ ℂ^n) :
  ∥ x ∥^2 = ∥ (orthogonal_projection S).to_linear_map x ∥^2 + ∥ (orthogonal_projection Sᗮ).to_linear_map x ∥^2 :=
begin
  let p1 := (orthogonal_projection S).to_linear_map,
  let p2 := (orthogonal_projection Sᗮ).to_linear_map,
  have x_decomp : x = (p1 x : ℂ^n) + (p2 x) :=  
    eq_sum_orthogonal_projection_self_orthogonal_complement S x,    
  have x_orth : ⟪ (p1 x : ℂ^n), p2 x ⟫_ℂ = 0 :=
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
  rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((p1 x) : ℂ^n) (p2 x) x_orth,
  simp only [add_left_inj,
    mul_eq_mul_left_iff,
    norm_eq_zero,
    true_or,
    eq_self_iff_true,
    submodule.coe_norm,
    submodule.coe_eq_zero],
end

noncomputable def linear_isometry_extend (L : S →ₗᵢ[ℂ] ℂ^n): (ℂ^n) →ₗᵢ[ℂ] (ℂ^n) :=
begin
  let p1 := (orthogonal_projection S).to_linear_map,
  let p2 := (orthogonal_projection Sᗮ).to_linear_map,
  have : (finrank ℂ Sᗮ) = (finrank ℂ Sᗮ) := rfl,
  let L2_first := (linear_isometry_equiv.of_inner_product_space this).to_linear_isometry,
  let L2_next := (linear_isometry_equiv.of_inner_product_space (finrank_orthogonal_range_of_inj L.injective)).symm.to_linear_isometry,
  let L2 := (L.to_linear_map.range)ᗮ.subtypeₗᵢ.comp (L2_next.comp L2_first),
  let M := L.to_linear_map.comp p1 + L2.to_linear_map.comp p2,
  have : linear_isometry _ (ℂ^n) (ℂ^n) :=
  {
    to_linear_map := M,
    norm_map' := _,
  },
  exact this,
  intro x,

  have Mx_decomp : M x = L (p1 x) + L2 (p2 x) :=
  begin
    simp only [linear_map.add_apply],
    rw [linear_map.comp_apply, linear_map.comp_apply],
    simp only [linear_isometry.coe_to_linear_map],
  end,
  have Mx_orth : ⟪ L (p1 x), L2 (p2 x) ⟫_ℂ = 0 :=
  begin
    have Lp1x : L (p1 x) ∈ L.to_linear_map.range := L.to_linear_map.mem_range_self (p1 x),
    have Lp2x : L2 (p2 x) ∈ (L.to_linear_map.range)ᗮ :=
    begin
      simp only [L2],
      simp only [linear_isometry.coe_comp,
      function.comp_app,
      submodule.coe_subtypeₗᵢ],
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
  rw norm_sq_eq_norm_sq_proj_orthogonal x S,
  simp only [sq],
  rw Mx_decomp,
  rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L2 (p2 x)) Mx_orth,
  simp only [linear_isometry.norm_map],
  exact norm_nonneg _,
  exact norm_nonneg _,
end
