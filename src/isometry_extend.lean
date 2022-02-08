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
  sorry,
end 

lemma LSperp_dim : finite_dimensional.finrank ℂ (image_of S L)ᗮ = codim S :=
begin
  sorry,
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

noncomputable def L' := (image_of S L)ᗮ.subtypeₗᵢ.comp (complementary_isometry S L).some

theorem isometry_extend : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
begin
  let M := L.to_linear_map.comp (orthogonal_projection S).to_linear_map
            + (L' S L).to_linear_map.comp (orthogonal_projection Sᗮ).to_linear_map,
  use M,
  intro x,
  have : ∥ M x ∥^2 = ∥ x ∥^2 :=
  begin
    sorry,
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
