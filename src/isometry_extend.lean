/-
The goal of this file is to prove the following.  If S ⊆ ℂ^n is a subspace and L : S → V is
an isometry, then there exists an isometry M : ℂ^n → ℂ^n such that M(s) = L(s) for every s ∈ S.
-/

import analysis.inner_product_space.pi_L2
open_locale complex_conjugate

variable {n : ℕ}

local notation `ℂ^` n := euclidean_space ℂ (fin n)

variables (S : submodule ℂ (ℂ^n)) (L : S →ₗᵢ[ℂ] ℂ^n)

local notation `dim ` S := finite_dimensional.finrank ℂ S

local notation `range ` L := L.to_linear_map.range

local notation `proj ` S := orthogonal_projection S

/-
dim L(S) = dim S
-/
lemma dim_range_eq_dim : (dim (range L)) = (dim S) :=
begin
  have equiv_of_image := linear_equiv.of_injective (L.to_linear_map) L.injective,
  have : (dim S) = (dim (range L)) :=
  begin
    apply finite_dimensional.nonempty_linear_equiv_iff_finrank_eq.1,
    use equiv_of_image,
    exact finite_dimensional.finite_dimensional_submodule S,
    exact finite_dimensional.finite_dimensional_submodule (L.to_linear_map).range,
  end,
  rw this,
end 

/-
(dim Sᗮ) = (dim ℂ^n) - (dim S)
-/
lemma finrank_orthogonal_eq_finrank_sub (S : submodule ℂ (ℂ^n)) :
  (dim Sᗮ) = (dim ℂ^n) - (dim S) :=
begin
  have : (dim S) + (dim Sᗮ) = (dim ℂ^n) := S.finrank_add_finrank_orthogonal,
  symmetry,
  rw nat.sub_eq_iff_eq_add,
  rw add_comm,
  symmetry,
  exact this,
  apply submodule.finrank_le,
end

/-
dim L(S)ᗮ = dim Sᗮ
-/
lemma dim_orthogonal_range_eq_dim_orthogonal : (dim (range L)ᗮ) = (dim Sᗮ) :=
begin
  exact calc (dim (range L)ᗮ) = (dim ℂ^n) - (dim (range L)) : finrank_orthogonal_eq_finrank_sub (range L)
  ...                         = (dim ℂ^n) - (dim S)         : by rw dim_range_eq_dim
  ...                         = (dim Sᗮ)                     : by rw ← finrank_orthogonal_eq_finrank_sub S,
end

/-
We have an isometry L' between Sᗮ and L(S)ᗮ by mapping through Euclidean space.
-/
lemma complementary_isometry : ∃ (L' : (Sᗮ →ₗᵢ[ℂ] (range L)ᗮ)), true :=
begin
  have : (dim Sᗮ) = (dim Sᗮ) := by simp only [eq_self_iff_true],
  let L1 := (linear_isometry_equiv.of_inner_product_space this).to_linear_isometry,
  let L2 := (linear_isometry_equiv.of_inner_product_space (dim_orthogonal_range_eq_dim_orthogonal S L)).symm.to_linear_isometry,
  use (L2.comp L1),
end

noncomputable def L' := (range L)ᗮ.subtypeₗᵢ.comp (complementary_isometry S L).some

/-
We build a linear map on ℂ^n by projecting and applying our isometries.
-/

noncomputable def extend_L_L' :=
  L.to_linear_map.comp (proj S).to_linear_map + (L' S L).to_linear_map.comp (proj Sᗮ).to_linear_map

/-
The Pythagorean theorem, applied to members of S and Sᗮ.
-/
lemma norm_add_sq_orthogonal (x y : ℂ^n) (hx : x ∈ S) (hy : y ∈ Sᗮ) : ∥ x + y ∥^2 = ∥ x ∥^2 + ∥ y ∥^2 :=
begin
  iterate {rw sq},  
  apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y (submodule.inner_right_of_mem_orthogonal hx hy),
end

/-
The extension (extend_L_L' S L) is an isometry.
-/
lemma extension_isometry : ∀ (x : ℂ^n), ∥ (extend_L_L' S L) x ∥^2 = ∥ x ∥^2 :=
begin
  intro x,
  have x_decomp : x = ↑((proj S) x) + ↑((proj Sᗮ) x) := eq_sum_orthogonal_projection_self_orthogonal_complement S x,
  conv
  begin
    to_rhs,
    rw x_decomp,
  end,
  have h_xS : ↑((proj S) x) ∈ S := set_like.coe_mem ((proj S) x),
  have h_xSperp : ↑((proj Sᗮ) x) ∈ Sᗮ := set_like.coe_mem ((proj Sᗮ) x),
  rw norm_add_sq_orthogonal S ((proj S) x) ((proj Sᗮ) x) h_xS h_xSperp,

  have Mx_decomp : (extend_L_L' S L) x = L ((proj S) x) + (L' S L)((proj Sᗮ) x) :=
  begin
    rw extend_L_L',
    simp only [linear_isometry.coe_to_linear_map, continuous_linear_map.to_linear_map_eq_coe,
      add_left_inj, eq_self_iff_true, function.comp_app, linear_map.coe_comp, linear_isometry.map_eq_iff,
      continuous_linear_map.coe_coe, linear_map.add_apply],
  end,
  rw Mx_decomp,
  have h_Lx : L ((proj S) x) ∈ (range L) := L.to_linear_map.mem_range_self ((proj S) x),
  have h_L'x : (L' S L)((proj Sᗮ) x) ∈ (range L)ᗮ :=
  begin
    rw L',
    simp only [ submodule.subtype_apply, linear_isometry.coe_comp,
      function.comp_app, submodule.coe_mem, submodule.coe_subtypeₗᵢ ],
  end,
  rw norm_add_sq_orthogonal (range L) (L ((proj S) x)) ((L' S L) ((proj Sᗮ) x)) h_Lx h_L'x,
  simp only [linear_isometry.norm_map, submodule.coe_norm],
end

/-
The extension (extend_L_L' S L) agrees with L on S.
-/
theorem isometry_extend : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
begin
  let M := (extend_L_L' S L),
  use M,
  have : ∀ (x : ℂ^n), ∥ M x ∥^2 = ∥ x ∥^2 := extension_isometry S L,
  intro x,
  specialize this x,
  rw sq_eq_sq at this,
  exact this,
  exact norm_nonneg _,
  exact norm_nonneg _,
  intro s,
  rw ← linear_isometry.coe_to_linear_map,
  simp only [M],
  rw extend_L_L',
  simp only [add_right_eq_self, linear_isometry.coe_to_linear_map, continuous_linear_map.to_linear_map_eq_coe,
    function.comp_app, orthogonal_projection_mem_subspace_eq_self, linear_map.coe_comp,
    continuous_linear_map.coe_coe,
    linear_map.add_apply],
  rw orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
  simp only [eq_self_iff_true, linear_isometry.map_zero],
  simp only [submodule.orthogonal_orthogonal, submodule.coe_mem],
end
