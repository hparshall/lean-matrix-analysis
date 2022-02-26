-- import .gram_sqrt
import .isometry_extend
import .square_root_def

localized "postfix `†`:1000 := linear_map.adjoint" in src
-- variable {n : ℕ}
-- variable T : Lℂ^n
variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] [decidable_eq 𝕜]
variables {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)
variables {T : E →ₗ[𝕜] E}
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
namespace inner_product_space

-- below three lemmas are current PRs, here only for refactor
lemma is_self_adjoint_adjoint_mul_self (T : E →ₗ[𝕜] E) : is_self_adjoint (T.adjoint * T) :=
λ x y, by simp only [linear_map.mul_apply, linear_map.adjoint_inner_left,
  linear_map.adjoint_inner_right]

lemma re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) :
  0 ≤ is_R_or_C.re ⟪ x, (T.adjoint * T) x ⟫ := by {simp only [linear_map.mul_apply,
  linear_map.adjoint_inner_right, inner_self_eq_norm_sq_to_K], norm_cast, exact sq_nonneg _}

lemma has_eigenvalue_eigenvalues (hT: is_self_adjoint T) (i : fin n) :
  module.End.has_eigenvalue T (hT.eigenvalues hn i) :=
  module.End.has_eigenvalue_of_has_eigenvector (hT.has_eigenvector_eigenvector_basis hn i)
-- above three lemmas are current PRs, here only for refactor

lemma gram_sa (T : E →ₗ[𝕜] E): is_self_adjoint (T† * T) := is_self_adjoint_adjoint_mul_self T

lemma gram_nn (T : E →ₗ[𝕜] E): ∀ (i : (fin n)), 0 ≤ (gram_sa T).eigenvalues hn i :=
begin
  intro i,
  let := has_eigenvalue_eigenvalues hn (gram_sa T) i,
  apply eigenvalue_nonneg_of_nonneg (has_eigenvalue_eigenvalues hn (gram_sa T) i),
  apply re_inner_adjoint_mul_self_nonneg,
end

/-- The square root of `T† * T` applied to any element has the same norm as just applying `T`. -/
lemma norm_apply_eq_norm_sqrt_apply (T : E →ₗ[𝕜] E): ∀ (v : E), ∥ T v ∥^2 = ∥ ((gram_sa T).sqrt hn) v ∥^2 :=
begin
  intro v,
  nth_rewrite 1 norm_sq_eq_inner,
  rw [(gram_sa T).sqrt_self_adjoint, ← linear_map.mul_apply,
    (gram_sa T).sqrt_mul_self_eq hn (gram_nn hn T), linear_map.mul_apply,
    linear_map.adjoint_inner_right, norm_sq_eq_inner],
end

lemma ker_eq_sqrt_ker (T : E →ₗ[𝕜] E) : T.ker = ((gram_sa T).sqrt hn).ker :=
begin
  ext,
  rw [linear_map.mem_ker, linear_map.mem_ker, ← @norm_eq_zero _ _ (T x), ← @norm_eq_zero _ _ ((gram_sa T).sqrt hn x)],
  rw (sq_eq_sq (norm_nonneg _) (norm_nonneg _)).1 (norm_apply_eq_norm_sqrt_apply hn T x),
end

/-- The isometry between the range of `sqrt (T† * T)` and the range of `T` given by:
  1. pulling back the range of `sqrt (T† * T)` to `E ⧸ (sqrt (T† *T )).ker`,
  2. identifying the kernels of `sqrt(T† * T)` and `T`,
  3. pushing forward from `E ⧸ T.ker` to `T.range`. -/
noncomputable def S₁ : ↥((gram_sa T).sqrt hn).range ≃ₗᵢ[𝕜] ↥(T.range) :=
{ to_linear_equiv :=
begin
  let T_first : (E ⧸  T.ker) ≃ₗ[𝕜] T.range := linear_map.quot_ker_equiv_range T,
  let Q_first : (E ⧸  ((gram_sa T).sqrt hn).ker) ≃ₗ[𝕜] ((gram_sa T).sqrt hn).range :=
    linear_map.quot_ker_equiv_range ((gram_sa T).sqrt hn),
  let same_quot : (E ⧸ ((gram_sa T).sqrt hn).ker) ≃ₗ[𝕜] (E ⧸ T.ker) :=
    submodule.quot_equiv_of_eq ((gram_sa T).sqrt hn).ker T.ker (ker_eq_sqrt_ker hn T).symm,
  exact (Q_first.symm).trans (same_quot.trans (T_first)),
end,
  norm_map' :=
  begin
    intro x,
    choose y hy using linear_map.mem_range.1 (subtype.mem x),
    simp only [linear_equiv.trans_apply, submodule.coe_norm],
    suffices : ((gram_sa T).sqrt hn).quot_ker_equiv_range.symm x = ((gram_sa T).sqrt hn).ker.mkq y,
    rw [this, ← hy],
    simp only [linear_map.quot_ker_equiv_range_apply_mk, submodule.mkq_apply, submodule.quot_equiv_of_eq_mk],
    exact (sq_eq_sq (norm_nonneg _) (norm_nonneg _)).1 (norm_apply_eq_norm_sqrt_apply hn T y),
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image,
    congr,
    simp only [set_like.eta, hy],
    simp only [exists_apply_eq_apply, linear_map.mem_range],
  end,
}


lemma S₁_map_to_sqrt_gram (T : E →ₗ[𝕜] E) : 
  ∀ x : E, T x = S₁ hn ((linear_map.range_restrict ((gram_sa T).sqrt hn)) x) :=
begin
  intro v,
  simp only [S₁, linear_equiv.trans_apply, linear_isometry_equiv.coe_mk],
  have : (linear_map.quot_ker_equiv_range ((gram_sa T).sqrt hn)).symm (linear_map.range_restrict ((gram_sa T).sqrt hn) v) = ((gram_sa T).sqrt hn).ker.mkq v :=
    by { rw ← linear_map.quot_ker_equiv_range_symm_apply_image ((gram_sa T).sqrt hn), congr' },
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