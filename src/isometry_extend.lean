import .lemmas.ladr_7_lem

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (S : submodule ℂ (ℂ^n)) (L : S →ₗᵢ[ℂ] ℂ^n)

noncomputable def image_of := L.to_linear_map.range

noncomputable def codim := finite_dimensional.finrank ℂ Sᗮ

lemma euclidean_codim : finite_dimensional.finrank ℂ (ℂ^(codim S)) = codim S := by simp only [fintype.card_fin, finrank_euclidean_space, eq_self_iff_true]

lemma Sperp_dim : finite_dimensional.finrank ℂ Sᗮ = codim S := by rw codim

lemma L1_to_euclidean : ∃ (L1 : (Sᗮ →ₗᵢ[ℂ] ℂ^(codim S))), true :=
begin
  let L1 := linear_isometry_equiv.of_inner_product_space (Sperp_dim S),
  use L1.to_linear_isometry,
end

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

lemma L2_to_euclidean : ∃ (L2 : ((image_of S L)ᗮ ≃ₗᵢ[ℂ] ℂ^(codim S))), true :=
begin
  let L2 := linear_isometry_equiv.of_inner_product_space (LSperp_dim S L),
  use L2,
end

lemma complementary_isometry : ∃ (L' : (Sᗮ →ₗᵢ[ℂ] (image_of S L)ᗮ)), true :=
begin
  let L1 := (L1_to_euclidean S).some,
  let L2 := (L2_to_euclidean S L).some.symm.to_linear_isometry,
  use (L2.comp L1),
end

lemma orth_proj_perp_eq_zero (x : S) : (orthogonal_projection Sᗮ) ↑x = 0 :=
begin
  have : ↑x ∈ S := submodule.coe_mem x,
  exact orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero this,
end

lemma orth_perp_proj_eq_zero (y : Sᗮ) : (orthogonal_projection Sᗮᗮ) ↑y = 0 :=
begin
  have : ↑y ∈ Sᗮ := submodule.coe_mem y,
  exact orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero this,
end

lemma S_perp_perp : Sᗮᗮ = S :=
begin
  exact submodule.orthogonal_orthogonal S,
end

lemma norm_of_sum_perp (x : S) (y : Sᗮ) : ∥ (↑x : ℂ^n) + ↑y ∥^2 = ∥ x ∥^2 + ∥ y ∥^2 :=
begin
  rw sq,
  rw orthogonal_projection_fn_norm_sq Sᗮ (↑x + y),
  simp only [map_add,
 add_sub_add_left_eq_sub,
 submodule.subtype_apply,
 orthogonal_projection_fn_eq,
 submodule.coe_add,
 orthogonal_projection_mem_subspace_eq_self],
  rw orth_proj_perp_eq_zero,
  simp only [submodule.norm_coe, add_sub_cancel, zero_add, submodule.coe_zero],
  rw [sq, sq],
end

lemma norm_of_sum_perp' (x y : ℂ^n) (hx : x ∈ S) (hy : y ∈ Sᗮ) : ∥ x + y ∥^2 = ∥ x ∥^2 + ∥ y ∥^2 :=
begin
  have xy_perp : ⟪x , y⟫_ℂ = 0 :=
  begin
    calc ⟪ x, y ⟫_ℂ = ⟪ x - 0 , y ⟫_ℂ : by {congr, simp only [eq_self_iff_true, sub_zero]}
    ...             = ⟪ x - ((orthogonal_projection Sᗮ) x) , y ⟫_ℂ : by {congr, rw orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero hx, norm_cast}
    ...             = 0 : orthogonal_projection_inner_eq_zero x y hy,
  end,
  have yx_perp : ⟪ y , x ⟫_ℂ = 0 :=
  begin
    calc ⟪ y, x ⟫_ℂ = conj ⟪ x, y⟫_ℂ : by {rw inner_product_space.conj_sym}
    ...             = conj 0 : by {rw xy_perp}
    ...             = 0 : by {simp only [eq_self_iff_true, map_zero]},
  end,
  have : (∥ x + y ∥^2 : ℂ) = ∥ x ∥^2 + ∥ y ∥^2 :=
  begin
  calc (∥ x + y ∥^2 : ℂ) = ⟪ x + y , x + y ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
  ...              = ⟪ x , x ⟫_ℂ + ⟪ x , y ⟫_ℂ + ⟪ y , x ⟫_ℂ + ⟪ y , y ⟫_ℂ : by {rw inner_add_add_self}
  ...              = ⟪ x , x ⟫_ℂ + ⟪ y , y ⟫_ℂ : by {rw xy_perp, rw yx_perp, ring}
  ...              = ∥ x ∥^2 + ∥ y ∥^2 : by {rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K]},
  end,
  rw ← complex.of_real_inj,
  simp [this],
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
    rw norm_of_sum_perp S ((orthogonal_projection S) x) ((orthogonal_projection Sᗮ) x),

    rw @norm_split_L_L' _ S L ((orthogonal_projection S) x) ((orthogonal_projection Sᗮ) x),
    simp only [linear_isometry.norm_map, add_left_inj, eq_self_iff_true, sq_eq_sq],
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
