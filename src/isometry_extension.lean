import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.inner_product_space.l2_space
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem
import .linear_independent

variable {n : ℕ}
variable T : Lℂ^n
-- Dan's work on trying to extend isometries
-- example (M : submodule ℂ ℂ^n) (S₀ : M →ₗᵢ[ℂ] M) : ∃ S : (ℂ^n) →ₗᵢ[ℂ] ℂ^n, orthogonal_projection M ∘ (linear_map.dom_restrict S.to_linear_map M) = S₀ :=
-- begin
--   have exists_w := exists_hilbert_basis ℂ M,
--   let w'' := classical.some exists_w,
--   let b₀ : hilbert_basis w'' ℂ M := classical.some (classical.some_spec exists_w),

--   let w' : set (ℂ^n) := sorry,
--   let b' : w' → (ℂ^n) := coe,
--   have : orthonormal ℂ (coe : w' → ℂ^n) := sorry,
--   have : ∃ (w : set ℂ^n) (b : hilbert_basis w ℂ ℂ^n), w' ⊆ w ∧ ⇑b = (coe : w → ℂ^n) := orthonormal.exists_hilbert_basis_extension this,

-- end

#check T.range_restrict


open classical 
universe u

variable S : submodule ℂ ℂ^n

variable (L : S →ₗᵢ[ℂ] ℂ^n)

variable w' : orthonormal_basis_index ℂ ↥S
#check ⇑(orthonormal_basis ℂ ↥S)

-- lemma L_to_M : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
-- begin
--   let m := finite_dimensional.finrank ℂ S,
--   have S_rank_m : finite_dimensional.finrank ℂ S = m := rfl,

--   let b' := orthonormal_basis ℂ S,
--   -- have hb' : orthonormal ℂ b' := fin_orthonormal_basis_orthonormal S_rank_m,
--   -- simp only [b'] at hb',
--   -- rw coe_orthonormal_basis at hb',  
--   have b'_lifts_to_coe := coe_orthonormal_basis ℂ S,
--   let foo := ⇑b',
--   have hfoo : orthonormal ℂ foo :=
--   begin
--     apply orthonormal_basis_orthonormal,
--   end,
--   rw orthonormal at hfoo,
--   let foo₂ := S.subtype ∘ foo,
--   have : orthonormal ℂ foo₂ :=
--   begin
--     rw orthonormal,
--     simp only [foo₂],
--     simp only [set_coe.forall],
--     simp? [hfoo],
--   end,
--   have b'_orthonormal := orthonormal_basis_orthonormal ℂ ℂ^n,


--   -- rw b'_lifts_to_coe at b'_orthonormal,

--   -- have exists_extension := exists_subset_is_orthonormal_basis b'_orthonormal,


-- end

-- lemma onb_coe_to_onf : orthonormal ℂ (S.subtype ∘ orthonormal_basis ℂ S) :=
-- begin
--   rw orthonormal_iff_ite,
--   intros i j,
--   rw function.comp_app,
--   rw function.comp_app,
--   rw submodule.subtype_apply,
--   rw submodule.subtype_apply,
--   rw ← submodule.coe_inner,
--   revert i j,
--   rw ← orthonormal_iff_ite,
--   apply orthonormal_basis_orthonormal ℂ,
-- end

-- lemma L_to_M : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
-- begin
--   let m := finite_dimensional.finrank ℂ S,
--   have S_rank_m : finite_dimensional.finrank ℂ S = m := rfl,

--   -- Taking an onb for S
--   let b' := orthonormal_basis ℂ S,
--   have b'_lifts_to_coe := coe_orthonormal_basis ℂ S,
--   let b'_in_Cn := S.subtype ∘ ⇑b',
--   have b'_orthonormal : orthonormal ℂ b'_in_Cn := onb_coe_to_onf S,
--   have b'_in_Cn_is_coe : b'_in_Cn = coe :=
--   begin
--     simp only [b'_in_Cn],
--     simp only [coe_orthonormal_basis],
--     ext1,
--     simp only [submodule.subtype_apply, eq_self_iff_true, function.comp_app, set_like.coe_eq_coe, coe_coe],
--   end,

--   let Lb' := L ∘ ⇑b',

--   have Lb'_orthonormal := lin_iso_preserves_on (⇑b') b'_orthonormal L,

--   let Lw' := set.range Lb',
--   let Lb'' : Lw' → ℂ^n := coe,
--   have Lb''_orthonormal : orthonormal ℂ Lb'' := sorry,
--   simp only [Lb''] at Lb''_orthonormal,

--   rw b'_in_Cn_is_coe at b'_orthonormal,
-- -- orthonormal ℂ Lb'
--   -- Extending b' to b
--   have b_exists := @exists_subset_is_orthonormal_basis ℂ (ℂ^n) complex.is_R_or_C _ _ _ b'_orthonormal,

--   have b_exists' := some_spec b_exists,
--   have b_exists'' := some_spec b_exists',
--   let b := some b_exists'',
--   have hb : orthonormal ℂ b ∧ ⇑b = coe := some_spec b_exists'',

--   have Lb_exists := @exists_subset_is_orthonormal_basis ℂ _ _ _ _ _ Lb''_orthonormal,

--   have Lb_exists' := some_spec Lb_exists,
--   have Lb_exists'' := some_spec Lb_exists',
--   let Lb := some Lb_exists'',
--   have hLb : orthonormal ℂ Lb ∧ ⇑Lb = coe := some_spec Lb_exists'',
--   let M := basis.constr b ℂ,
-- end


-- example {S : submodule ℂ ℂ^n} (L : S →ₗᵢ[ℂ] ℂ^n) : 1 = 2 :=
-- begin
--   -- First we find an orthonormal basis over S,
--   have exists_w' := exists_hilbert_basis ℂ S,
--   let w' := some exists_w',
--   let b' : hilbert_basis w' ℂ S := some (some_spec exists_w'),
--   have hb' : ⇑b' = coe := some_spec (some_spec exists_w'),
--   -- Now extend the basis to ℂⁿ:
--   have b'_orthonormal : orthonormal ℂ (coe : ↥w' → ↥S) :=
--   begin
--     rw ← hb',
--     exact b'.orthonormal,
--   end,
--   have b'_extends := orthonormal.exists_hilbert_basis_extension b'_orthonormal,
--   let w := some b'_extends,
--   have hw := some_spec b'_extends,
--   let b := some hw,
--   have hb : w' ⊆ w ∧ ⇑b = coe := some_spec hw,

--   -- Now we map the smaller basis into ℂⁿ by L:
--   let Lb' := L ∘ (⇑b'),
--   have Lb'_orthonormal : orthonormal ℂ Lb' := lin_iso_preserves_on (⇑b') b'.orthonormal L,
--   let Lw' := set.range Lb',
--   let Lb'' : Lw' → ℂ^n := coe,
--   have Lb''_orthonormal : orthonormal ℂ Lb'' := 
--   begin
--     sorry,
--   end,
--   -- And extend this new basis:
--   have Lb'_extends := orthonormal.exists_hilbert_basis_extension Lb''_orthonormal,
--   let Lw := some Lb'_extends,
--   have hLw := some_spec Lb'_extends,
--   let Lb := some hLw,
--   have hLb : Lw' ⊆ Lw ∧ ⇑Lb = coe := some_spec hLw,
--   let M := constr b ℂ,
-- end


noncomputable lemma eq_dim_has_lin_iso (S₁ S₂ : submodule ℂ ℂ^n) (h : finite_dimensional.finrank ℂ S₁ = finite_dimensional.finrank ℂ S₂) : S₁ →ₗᵢ[ℂ] S₂ :=
begin
  let d := finite_dimensional.finrank ℂ S₁,
  have hS₁ : finite_dimensional.finrank ℂ S₁ = d := rfl,
  have hS₂ : finite_dimensional.finrank ℂ S₂ = d := by {rw ← h},
  have S₁_equiv := linear_isometry_equiv.of_inner_product_space hS₁,
  have S₂_equiv := linear_isometry_equiv.of_inner_product_space hS₂,
  exact ((S₁_equiv).trans (S₂_equiv.symm)).to_linear_isometry,
end


noncomputable def d := finite_dimensional.finrank ℂ S
lemma dim_of_lin_iso : finite_dimensional.finrank ℂ (L.to_linear_map).range = (d S) :=
begin
  have equiv_of_image := linear_equiv.of_injective (L.to_linear_map) L.injective,

  have : finite_dimensional.finrank ℂ ↥S = finite_dimensional.finrank ℂ ↥(L.to_linear_map).range :=
  begin
    apply finite_dimensional.nonempty_linear_equiv_iff_finrank_eq.1,
    use equiv_of_image,
    exact finite_dimensional.finite_dimensional_submodule S,
    exact finite_dimensional.finite_dimensional_submodule (L.to_linear_map).range,
  end,
  rw ← this,
  simp only [d],
end

lemma L_to_M : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
begin
  let LS := (L.to_linear_map).range,
  have dim_LS_perp : finite_dimensional.finrank ℂ (LSᗮ) = n - (d S) :=
  begin
    rw ← dim_of_lin_iso S L,
    have dim_sum := submodule.finrank_add_finrank_orthogonal LS,
    rw @finrank_euclidean_space_fin ℂ _ n at dim_sum,
    have LS_dim_d : finite_dimensional.finrank ℂ (LS) = d S :=
    begin
      exact dim_of_lin_iso S L,
    end, 
    rw LS_dim_d at dim_sum,
    rw LS_dim_d,
    -- simp [dim_sum],
    -- have sum_dim := eq.symm dim_sum,
    -- rw sum_dim,

    sorry,
  end,
  have dim_LS : finite_dimensional.finrank ℂ Sᗮ = n - (d S) := sorry,
  

end
