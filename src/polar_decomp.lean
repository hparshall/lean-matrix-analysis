import .gram_sqrt
import .isometry_extend

localized "postfix `†`:1000 := linear_map.adjoint" in src
-- variable {n : ℕ}
-- variable T : Lℂ^n
variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {n : ℕ} {E : Type*} [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
variables {T : E →ₗ[𝕜] E}
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
namespace inner_product_space

def is_positive' (T : E →ₗ[𝕜] E) : Prop := 
  ∀ x : E, (is_R_or_C.re ⟪T x, x⟫ ≥ 0)

-- noncomputable def sqrt' (T : Lℂ^n) : Lℂ^n := classical.some (sqrt_gram_exists T)
def sqrt' (T : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := sorry

-- local notation `R` := (sqrt' T)

-- lemma R_sa : is_sa R :=
-- begin
--   have : (R^2 = T† * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram_exists T),
--   exact this.2.1,
-- end

lemma sqrt'_is_self_adjoint (T : E →ₗ[𝕜] E) : is_self_adjoint (sqrt' T) := sorry
lemma sqrt'_sq (T : E →ₗ[𝕜] E) : (sqrt' T) * (sqrt' T) = T  := sorry
lemma sqrt'_pos (T : E →ₗ[𝕜] E) : is_positive' (sqrt' T) := sorry

-- lemma R_mul_mul : R * R = T† * T :=
-- begin
--   have : (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram_exists T),
--   exact this.1,
-- end

-- lemma R_pos : is_positive R :=
-- begin
--   have : (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram_exists T),
--   exact this.2.2,
-- end

/-- The square root of `T† * T` applied to any element has the same norm as just applying `T`. -/
lemma norm_apply_eq_norm_sqrt_apply (T : E →ₗ[𝕜] E): ∀ (v : E), ∥ T v ∥^2 = ∥ (sqrt' (T† * T)) v ∥^2 :=
begin
  intro v,
  apply is_R_or_C.of_real_inj.1,
  calc ↑(∥ T v ∥^2) = ⟪ T v , T v ⟫ : by {rw inner_self_eq_norm_sq_to_K, norm_cast}
    ...          = ⟪ T† (T v), v ⟫ : by {rw linear_map.adjoint_inner_left}
    ...          = ⟪ (T† * T) v, v ⟫ : by {rw linear_map.mul_apply}
    ...          = ⟪ (sqrt' (T† * T) * (sqrt' (T† * T))) v, v ⟫ : by {rw sqrt'_sq (T† * T)}
    ...          = ⟪ sqrt' (T† * T) v, sqrt' (T† * T) v ⟫ : 
      by {rw linear_map.mul_apply, rw ← linear_map.adjoint_inner_left,
        rw ← (linear_map.is_self_adjoint_iff_eq_adjoint (sqrt' (T† * T))).1 (sqrt'_is_self_adjoint (T†*T))}
    ...          = ↑(∥ sqrt' (T† * T) v ∥^2) : by {rw inner_self_eq_norm_sq_to_K, norm_cast},
end

lemma ker_eq_sqrt_ker (T : E →ₗ[𝕜] E) : T.ker = (sqrt' (T† * T)).ker :=
begin
  ext,
  rw [linear_map.mem_ker, linear_map.mem_ker, ← @norm_eq_zero _ _ (T x), ← @norm_eq_zero _ _ (sqrt' (T† * T) x)],
  rw (sq_eq_sq (norm_nonneg _) (norm_nonneg _)).1 (norm_apply_eq_norm_sqrt_apply T x),
end

/-- The isometry between the range of `sqrt (T† * T)` and the range of `T` given by:
  1. pulling back the range of `sqrt (T† * T)` to `E ⧸ (sqrt (T† *T )).ker`,
  2. identifying the kernels of `sqrt(T† * T)` and `T`,
  3. pushing forward from `E ⧸ T.ker` to `T.range`. -/
noncomputable def S₁ : ↥(sqrt' (T† * T)).range ≃ₗᵢ[𝕜] ↥(T.range) :=
{ to_linear_equiv :=
begin
  let T_first : (E ⧸  T.ker) ≃ₗ[𝕜] T.range := linear_map.quot_ker_equiv_range T,
  let Q_first : (E ⧸  (sqrt' (T† * T)).ker) ≃ₗ[𝕜] (sqrt' (T† * T)).range :=
    linear_map.quot_ker_equiv_range (sqrt' (T† * T)),
  let same_quot : (E ⧸ (sqrt' (T† * T)).ker) ≃ₗ[𝕜] (E ⧸ T.ker) :=
    submodule.quot_equiv_of_eq (sqrt' (T† * T)).ker T.ker (ker_eq_sqrt_ker T).symm,
  exact (Q_first.symm).trans (same_quot.trans (T_first)),
end,
  norm_map' :=
  begin
    intro x,
    have x_mem : ↑x ∈ (sqrt' (T† * T)).range := subtype.mem x,
    rw linear_map.mem_range at x_mem,
    choose y hy using x_mem,
    simp only [linear_equiv.trans_apply, submodule.coe_norm],
    suffices : (sqrt' (T† * T)).quot_ker_equiv_range.symm x = (sqrt' (T† * T)).ker.mkq y,
    rw [this, ← hy],
    simp only [linear_map.quot_ker_equiv_range_apply_mk, submodule.mkq_apply, submodule.quot_equiv_of_eq_mk],
    exact (sq_eq_sq (norm_nonneg _) (norm_nonneg _)).1 (norm_apply_eq_norm_sqrt_apply T y),
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image,
    congr,
    simp only [set_like.eta, hy],
    simp only [exists_apply_eq_apply, linear_map.mem_range],
  end,
}


lemma S₁_map_to_sqrt_gram (T : E →ₗ[𝕜] E): ∀ x : E, T x = S₁ ((linear_map.range_restrict (sqrt' (T† * T))) x) :=
begin
  intro v,
  rw S₁,
  simp only [linear_equiv.trans_apply, linear_isometry_equiv.coe_mk],
  have : (linear_map.quot_ker_equiv_range (sqrt' (T† * T))).symm (linear_map.range_restrict (sqrt' (T† * T)) v) = (sqrt' (T† * T)).ker.mkq v :=
  begin
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image (sqrt' (T† * T)),
    congr',
  end,
  rw this,
  simp only [linear_map.quot_ker_equiv_range_apply_mk,
 submodule.mkq_apply,
 submodule.quot_equiv_of_eq_mk],
end

-- extension still wants the new version of isometry_extend.
lemma lem_7_45 : ∃ (S : linear_isometry (ring_hom.id ℂ) (ℂ^n) (ℂ^n)), ∀ v : ℂ^n, (T v = S (R v)) :=
begin
  have key := lem_7_45_2 T,
  let S₁ := classical.some key,
  let hS₁ : ∀ v, (S₁ ((linear_map.range_restrict R) v): ℂ^n) = T v := classical.some_spec key,

  let inclusion : (T.range) →ₗᵢ[ℂ]  (ℂ^n) := submodule.subtypeₗᵢ T.range,
  let S' : ((R).range) →ₗᵢ[ℂ] (ℂ^n) := inclusion.comp (S₁.to_linear_isometry),

  let M := classical.some (isometry_extend (linear_map.range (R)) S'),
  have hM : (∀ (s : linear_map.range (R)), M s = S' s) := classical.some_spec (isometry_extend (linear_map.range (R)) S'),
  use M,
  intro v,
  specialize hM ((R).range_restrict v),
  simp only [submodule.subtype_apply,
 linear_isometry_equiv.coe_to_linear_isometry,
 linear_isometry.coe_comp,
 function.comp_app,
 linear_map.cod_restrict_apply,
 submodule.coe_subtypeₗᵢ] at hM,
 rw hM,
 rw hS₁ v,
end

end inner_product_space