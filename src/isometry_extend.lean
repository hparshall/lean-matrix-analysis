/-
The goal of this file is to prove the following.  If S ⊆ ℂ^n is a subspace and L : S → V is
an isometry, then there exists an isometry M : ℂ^n → ℂ^n such that M(s) = L(s) for every s ∈ S.
-/

import analysis.inner_product_space.pi_L2
open_locale complex_conjugate

notation `ℂ^` n := euclidean_space ℂ (fin n)

variables {n : ℕ} (S : submodule ℂ (ℂ^n)) (L : S →ₗᵢ[ℂ] ℂ^n)

noncomputable def image_of := L.to_linear_map.range

noncomputable def codim := finite_dimensional.finrank ℂ Sᗮ

lemma euclidean_codim : finite_dimensional.finrank ℂ (ℂ^(codim S)) = codim S := by simp only [fintype.card_fin, finrank_euclidean_space, eq_self_iff_true]

lemma Sperp_dim : finite_dimensional.finrank ℂ Sᗮ = codim S := by rw codim

/-
We have an isometry from Sᗮ to the appropriate Euclidean space.
-/
lemma L1_to_euclidean : ∃ (L1 : (Sᗮ →ₗᵢ[ℂ] ℂ^(codim S))), true :=
begin
  let L1 := linear_isometry_equiv.of_inner_product_space (Sperp_dim S),
  use L1.to_linear_isometry,
end

/-
The dimension of the image L(S) is equal to the dimension of S.
-/
lemma LS_dim : finite_dimensional.finrank ℂ (image_of S L) = finite_dimensional.finrank ℂ S :=
begin
  have equiv_of_image := linear_equiv.of_injective (L.to_linear_map) L.injective,

  have : finite_dimensional.finrank ℂ ↥S = finite_dimensional.finrank ℂ ↥(L.to_linear_map).range :=
  begin
    apply finite_dimensional.nonempty_linear_equiv_iff_finrank_eq.1,
    use equiv_of_image,
    exact finite_dimensional.finite_dimensional_submodule S,
    exact finite_dimensional.finite_dimensional_submodule (L.to_linear_map).range,
  end,
  rw this,
  rw image_of,
end 

/-
The orthogonal complement L(S)ᗮ has dimension equal to codim S.
-/
lemma LSperp_dim : finite_dimensional.finrank ℂ (image_of S L)ᗮ = codim S :=
begin
  have fact₁ := submodule.finrank_add_finrank_orthogonal (image_of S L),
  have fact₂ := submodule.finrank_add_finrank_orthogonal S,
  rw @LS_dim _ S L at fact₁,
  rw ← fact₁ at fact₂,
  have := add_left_cancel fact₂,
  rw codim,
  symmetry,
  exact this,
end 

/-
We have an isometry from L(S)ᗮ to the appropriate Euclidean space.
-/
lemma L2_to_euclidean : ∃ (L2 : ((image_of S L)ᗮ ≃ₗᵢ[ℂ] ℂ^(codim S))), true :=
begin
  let L2 := linear_isometry_equiv.of_inner_product_space (LSperp_dim S L),
  use L2,
end

/-
We have an isometry between Sᗮ and L(S)ᗮ by mapping through Euclidean space.
-/
lemma complementary_isometry : ∃ (L' : (Sᗮ →ₗᵢ[ℂ] (image_of S L)ᗮ)), true :=
begin
  let L1 := (L1_to_euclidean S).some,
  let L2 := (L2_to_euclidean S L).some.symm.to_linear_isometry,
  use (L2.comp L1),
end

/-
The projection of s ∈ S onto Sᗮ is zero.
-/
lemma orth_proj_perp_eq_zero (x : S) : (orthogonal_projection Sᗮ) ↑x = 0 :=
begin
  have : ↑x ∈ S := submodule.coe_mem x,
  exact orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero this,
end

/-
The Pythagorean theorem, applied to members of S and Sᗮ.
-/
lemma norm_of_sum_perp' (x y : ℂ^n) (hx : x ∈ S) (hy : y ∈ Sᗮ) : ∥ x + y ∥^2 = ∥ x ∥^2 + ∥ y ∥^2 :=
begin
  iterate {rw sq},  
  apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y (submodule.inner_right_of_mem_orthogonal hx hy),
end


noncomputable def L' := (image_of S L)ᗮ.subtypeₗᵢ.comp (complementary_isometry S L).some

lemma norm_split_L_L' (x : S) (y : Sᗮ) : ∥ (L x) + ((L' S L) y) ∥^2 = ∥ (L x) ∥^2 + ∥ ((L' S L) y) ∥^2 :=
begin
  have hLx : L x ∈ (image_of S L) :=
  begin
    rw image_of,
    simp only [exists_apply_eq_apply, linear_map.mem_range],
    use x,
    simp only [linear_isometry.coe_to_linear_map, eq_self_iff_true, linear_isometry.map_eq_iff],
  end,
  have hLy : (L' S L) y ∈ (image_of S L)ᗮ :=
  begin
    rw L',
    simp only [submodule.subtype_apply,
 linear_isometry.coe_comp,
 function.comp_app,
 submodule.coe_mem,
 submodule.coe_subtypeₗᵢ],
  end,
  exact norm_of_sum_perp' (image_of S L) (L x) ((L' S L) y) hLx hLy,
end

theorem isometry_extend : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
begin
  let M := L.to_linear_map.comp (orthogonal_projection S).to_linear_map
            + (L' S L).to_linear_map.comp (orthogonal_projection Sᗮ).to_linear_map,
  use M,
  intro x,
  have : ∥ M x ∥^2 = ∥ x ∥^2 :=
  begin
    have x_decomp : x = ↑((orthogonal_projection S) x) + ↑((orthogonal_projection Sᗮ) x) := eq_sum_orthogonal_projection_self_orthogonal_complement S x,
    have : M x = L ((orthogonal_projection S) x) + (L' S L)((orthogonal_projection Sᗮ) x) :=
    begin
      simp only [M],
      simp only [linear_isometry.coe_to_linear_map,
        continuous_linear_map.to_linear_map_eq_coe,
        add_left_inj,
        eq_self_iff_true,
        function.comp_app,
        linear_map.coe_comp,
        linear_isometry.map_eq_iff,
        continuous_linear_map.coe_coe,
        linear_map.add_apply],
    end,
    rw this,
    conv
    begin
      to_rhs,
      rw x_decomp,
    end,
    rw norm_of_sum_perp' S ((orthogonal_projection S) x) ((orthogonal_projection Sᗮ) x),
    rw @norm_split_L_L' _ S L ((orthogonal_projection S) x) ((orthogonal_projection Sᗮ) x),
    simp only [linear_isometry.norm_map, add_left_inj, eq_self_iff_true, sq_eq_sq],
    simp only [submodule.norm_coe, add_left_inj, eq_self_iff_true, sq_eq_sq],
    simp only [submodule.coe_mem],
    simp only [submodule.coe_mem],
  end,
  rw sq_eq_sq at this,
  exact this,
  exact norm_nonneg _,
  exact norm_nonneg _,
  intro s,
  rw ← linear_isometry.coe_to_linear_map,
  simp only [add_right_eq_self,
    linear_isometry.coe_to_linear_map,
    continuous_linear_map.to_linear_map_eq_coe,
    function.comp_app,
    orthogonal_projection_mem_subspace_eq_self,
    linear_map.coe_comp,
    continuous_linear_map.coe_coe,
    linear_map.add_apply],
  rw orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
  simp only [eq_self_iff_true, linear_isometry.map_zero],
  simp only [submodule.orthogonal_orthogonal, submodule.coe_mem],
end
