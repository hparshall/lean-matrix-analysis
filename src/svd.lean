import .gram_sqrt
import .polar_decomp

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (T : Lℂ^n)

local notation `R` := (sqrt' T)

noncomputable def singular_values : (fin n → ℝ) := (R_sa T).eigenvalues hn

noncomputable def e_basis : (basis (fin n) ℂ (ℂ^n)) := (gram_sa T).eigenvector_basis hn

noncomputable def S := classical.some (lem_7_45 T)

lemma lin_iso_preserves_onb' (b : basis (fin n) ℂ ℂ^n) (h : orthonormal ℂ b) : orthonormal ℂ ((S T) ∘ b) :=
begin
  unfold orthonormal,
  split,
  intro i,
  apply norm_sq_one_norm_eq_one,
  apply complex.of_real_injective,
  
  calc ↑(∥(⇑(S T) ∘ ⇑b) i∥ ^ 2) = (∥ ((S T) ∘ b) i ∥ : ℂ )^2 : by {simp only [complex.of_real_pow, linear_isometry_equiv.coe_to_linear_isometry, eq_self_iff_true, function.comp_app, linear_isometry_equiv.norm_map]}
    ...              = ↑∥ (S T) (b i) ∥^2 : by {simp only [linear_isometry_equiv.coe_to_linear_isometry, eq_self_iff_true, function.comp_app, linear_isometry_equiv.norm_map]}
    ...              = ⟪ (S T) (b i), (S T) (b i) ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
    ...              = ⟪ b i , b i ⟫_ℂ : by {rw linear_isometry.inner_map_map}
    ...              = (∥ b i ∥^2 : ℂ) : by {rw inner_self_eq_norm_sq_to_K}
    ...              = ((1 : ℝ) : ℂ) : by {rw h.1 i, simp only [one_pow, complex.of_real_one, eq_self_iff_true]},
  intros i j hij,
  rw linear_isometry.inner_map_map,
  exact h.2 hij,
end

lemma R_v_sum (v : ℂ^n) (R_is_sa : is_sa R) (h_fin : finite_dimensional.finrank ℂ (ℂ^n) = n): R v = ∑ (i : (fin n)), ⟪ (R_is_sa.eigenvector_basis h_fin i), v ⟫_ℂ • R (R_is_sa.eigenvector_basis h_fin i) :=
  begin
  let b := inner_product_space.is_self_adjoint.eigenvector_basis R_is_sa h_fin,
  have hb := inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal R_is_sa h_fin,
  conv
  begin
    to_lhs,
    rw onb_sum_repr b v hb,
    skip,
  end,
  calc R (∑ (i : fin n), ⟪ b i, v ⟫_ℂ • (b i)) = ∑ (i : fin n), R (⟪ b i, v ⟫_ℂ • (b i)) : by {rw linear_map.map_sum}
    ...                                        = ∑ (i : fin n), ⟪ b i, v ⟫_ℂ • R (b i) : by {simp only [is_R_or_C.inner_apply,
        inner_product_space.is_self_adjoint.apply_eigenvector_basis,
        pi_Lp.inner_apply,
        eq_self_iff_true,
        complex.coe_smul,
        linear_map.map_smul,
        finset.sum_congr]}
    ...           = ∑ (i : (fin n)), ⟪ (R_is_sa.eigenvector_basis h_fin i), v ⟫_ℂ • R (R_is_sa.eigenvector_basis h_fin i) : by {simp only [b]},
end


lemma h_fin : finite_dimensional.finrank ℂ (ℂ^n) = n :=
begin
  simp only [fintype.card_fin, finrank_euclidean_space, eq_self_iff_true],
end

lemma lin_ind (L : (ℂ^n) →ₗᵢ[ℂ] ℂ^n) (b : basis (fin n) ℂ ℂ^n) : linear_independent ℂ (L ∘ b) :=
begin
  apply linear_independent.map',
  exact b.linear_independent,

  rw linear_map.ker_eq_bot,
  exact L.injective,
end

lemma span (L : (ℂ^n) →ₗᵢ[ℂ] ℂ^n) (b : basis (fin n) ℂ ℂ^n) : submodule.span ℂ (set.range (L.to_linear_map ∘ b)) = ⊤ :=
begin
  let b' := (L ∘ b),
  have hlin := lin_ind L b,
  let b'' := basis.span hlin,
  rw set.range_comp,

  rw submodule.span_image (L.to_linear_map),
  rw b.span_eq,

  rw submodule.map_top,

  rw linear_map.range_eq_top,
  rw ← linear_map.injective_iff_surjective,
  have := linear_isometry.injective L,
  simp only [linear_isometry.coe_to_linear_map, this],
end

#check orthonormal_basis
noncomputable def svd_left (T : Lℂ^n) : orthonormal_basis (fin n) ℂ (ℂ^n) :=
begin
  have R_is_sa := R_sa T,
  exact (inner_product_space.is_self_adjoint.eigenvector_basis R_is_sa h_fin).to_orthonormal_basis (inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal R_is_sa h_fin),
end

noncomputable def svd_right (T : Lℂ^n) : orthonormal_basis (fin n) ℂ (ℂ^n) :=
begin
  have R_is_sa := R_sa T,
  let b' : basis (fin n) ℂ ℂ^n := inner_product_space.is_self_adjoint.eigenvector_basis R_is_sa h_fin,
  have hb' : orthonormal ℂ b' := inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal R_is_sa h_fin,
  let f' := (S T) ∘ b',
  have hsp : submodule.span ℂ (set.range f') = ⊤ := span (S T) b',
  have hon : orthonormal ℂ f' :=
  begin
    split,
    intro i,
    simp only [f'],
    rw function.comp_apply,
    rw (S T).norm_map,
    exact hb'.1 i,
    intros i j hij,
    simp only [f'],
    iterate {rw function.comp_apply},
    rw (S T).inner_map_map,
    exact hb'.2 hij,
  end,
  exact orthonormal_basis.mk hon hsp,
end

lemma S_left_eq_right (T : Lℂ^n) : (S T) ∘ (svd_left T) = svd_right T :=
begin
  simp only [svd_left, svd_right],
  simp only [orthonormal_basis.coe_mk, basis.coe_to_orthonormal_basis, eq_self_iff_true],
end

lemma sqrt_left_eig (T : Lℂ^n) (i : fin n) : (sqrt' T) (svd_left T i) = (singular_values T i) • (svd_left T i) :=
begin
  rw svd_left,
  simp only [inner_product_space.is_self_adjoint.apply_eigenvector_basis,
 basis.coe_to_orthonormal_basis,
 complex.coe_smul],
 congr,
end

lemma sqrt_eq_sum_inner_sing_left (v : ℂ^n) :
  (sqrt' T) v = ∑ (i : fin n), ⟪((svd_left T) i), v ⟫_ℂ • singular_values T i • (svd_left T) i :=
begin
  have := orthonormal_basis.sum_repr_symm (fin n) ℂ (ℂ^n) (svd_left T) ((svd_left T).repr v),
  rw linear_isometry_equiv.symm_apply_apply at this,
  conv_lhs {rw ← this},
  rw linear_map.map_sum,
  simp_rw linear_map.map_smul,
  simp_rw orthonormal_basis.repr_apply_apply,
  simp_rw sqrt_left_eig T _,
end


lemma iso_sqrt_eq_sum (v : ℂ^n) : (S T) (R v) = ∑ (i : fin n), ⟪ (svd_left T i), v ⟫_ℂ • (singular_values T i) • (S T) (svd_left T i) :=
begin
  calc (S T) (R v) = (S T) (∑ (i : fin n), ⟪ (svd_left T i), v ⟫_ℂ • (singular_values T i) • (svd_left T i)) : by {rw sqrt_eq_sum_inner_sing_left}
    ...           = (S T).to_linear_map (∑ (i : fin n), ⟪ (svd_left T i), v ⟫_ℂ • (singular_values T i) • (svd_left T i)) : by {congr}
    ...           = ∑ (i : fin n), ⟪ (svd_left T i), v ⟫_ℂ •  (singular_values T i) • (S T) (svd_left T i) : by {simp_rw [(S T).to_linear_map.map_sum, (S T).to_linear_map.map_smul, linear_map.map_smul_of_tower, linear_isometry.coe_to_linear_map]},
end

theorem svd_2 (T : Lℂ^n) : ∀ v : ℂ^n, 
  T v = ∑ (i : (fin n)), ⟪ (svd_left T) i, v ⟫_ℂ • singular_values T i • ((svd_right T) i) :=
begin
  have R_is_sa := R_sa T,
  intro v,
  rw ← S_left_eq_right,
  show T v = ∑ (i : fin n), ⟪ (svd_left T i), v ⟫_ℂ • (singular_values T i) • (S T) (svd_left T i),
  rw ← iso_sqrt_eq_sum,
  exact classical.some_spec (lem_7_45 T) v,
end


-- theorem svd (T : Lℂ^n) : ∃ e f : basis (fin n) ℂ (ℂ^n), 
--     (orthonormal ℂ e ∧ orthonormal ℂ f) ∧ ∀ v : ℂ^n, T v = ∑ (i : (fin n)), singular_values T i • ⟪e i, v ⟫_ℂ • (f i) :=
--   begin
--     have R_is_sa := R_sa T,
--     let b := inner_product_space.is_self_adjoint.eigenvector_basis R_is_sa h_fin,
--     have hb := inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal R_is_sa h_fin,

--     have hₛ : ∀ v : ℂ^n, (T v = (S T) (R v)) := classical.some_spec (lem_7_45 T),

--     let f' := (S T) ∘ b,
--     have hli : linear_independent ℂ f' := lin_ind ((S T)) b,
--     have hsp : submodule.span ℂ (set.range f') = ⊤ := span ((S T)) b,
--     let f := basis.mk hli hsp,

--     use b,
--     use f,

--     split,
--     split,
--     exact hb,

--     have : orthonormal ℂ (S T ∘ b) := lin_iso_preserves_onb' T b hb,
--     have f_def : (S T) ∘ b = f :=
--     begin
--       simp only [f],
--       rw basis.coe_mk,
--     end,
--     rw ← f_def,
--     exact this,

--     intro v,

--     have : R v = ∑ (i : (fin n)), ⟪ (b i), v ⟫_ℂ • (R (b i)) := R_v_sum T v R_is_sa _,

--     have eq₂ : (S T) (R v) = ∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • (S T) (R (b i)) :=
--       begin
--           calc (S T) (R v) = (S T) (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • R (b i)) : by {rw this}
--             ...        = (S T).to_linear_map (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • R (b i)) : by {norm_cast}
--             ...        = ∑ (i : fin n), (S T) (⟪ (b i), v ⟫_ℂ • R (b i)) : by {rw linear_map.map_sum, norm_cast}
--             ...        = (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • (S T) (R (b i))) : by {simp only [is_R_or_C.inner_apply,
--  inner_product_space.is_self_adjoint.apply_eigenvector_basis,
--  pi_Lp.inner_apply,
--  eq_self_iff_true,
--  complex.coe_smul,
--  linear_isometry.map_smul,
--  finset.sum_congr]},
--         end,
--     rw ← hₛ at eq₂,
--     rw eq₂,
--     have Sb_eq_f : ∀ i : (fin n),  (S T) (b i) = f i :=
--     begin
--       intro i,
--       rw basis.mk_apply hli hsp i,
--     end,
--     conv
--     {
--       to_lhs,
--       congr,
--       skip,
--       funext,
--       rw inner_product_space.is_self_adjoint.apply_eigenvector_basis R_is_sa,
--       norm_cast,
--       rw ← complex.coe_smul,
--       rw linear_isometry.map_smul (S T),
--       rw Sb_eq_f,
--     },
--     congr',
--     ext1,
--     have eq₃ : (ring_hom.id ℂ) ↑(R_is_sa.eigenvalues h_fin x) = singular_values T x :=
--     begin
--       simp only [complex.of_real_inj, ring_hom.id_apply],
--       unfold singular_values,
--     end,
--     simp only [is_R_or_C.inner_apply, basis.coe_mk, complex.coe_smul, finset.sum_congr],
--     rw smul_comm,
--     simp only [singular_values],
--   end
