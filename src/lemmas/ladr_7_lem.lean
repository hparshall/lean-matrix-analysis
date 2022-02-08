import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp

variable {n : ℕ}
def C : Type := euclidean_space ℂ (fin n)

notation `C` n := euclidean_space ℂ (fin n)
notation `ℂ^` n := euclidean_space ℂ (fin n)
notation `Lℂ^` n := module.End ℂ ℂ^n

notation `is_sa` := inner_product_space.is_self_adjoint
notation `I` := complex.I

localized "postfix `†`:1000 := linear_map.adjoint" in src

variable {T : module.End ℂ ℂ^n}

example (v : ℂ^n) : v = v :=
begin
  exact rfl,
end


lemma inner_with_all_eq_zero_eq_zero (v : ℂ^ n) : (∀ u : ℂ^n, ⟪u, v⟫_ℂ = 0) → v = 0 :=
begin
  intro h,
  by_contra',
  specialize h v,
  rw inner_self_eq_zero at h,
  exact this h,
end

lemma comp_eq_mul (A B : Lℂ^n) (v : ℂ^n) : A (B v) = (A * B) v := by {simp}
lemma comp_eq_mul' (A B : Lℂ^n) (v : ℂ^n) : (A.comp B) v = A (B v) := by {simp}
lemma comp_eq_mul'' (A B : Lℂ^n) : (A.comp B) = A * B := by {ext, rw ← comp_eq_mul, rw comp_eq_mul', rw ← comp_eq_mul, rw comp_eq_mul'}

lemma adjoint_prod (A B : Lℂ^n) : (A * B)† = B† * A† :=
begin
  rw ← comp_eq_mul'',
  rw linear_map.adjoint_comp,
  rw comp_eq_mul'',
end

lemma mul_adjoint (A B : Lℂ^n) : (A * B)† = B† * A† := adjoint_prod A B

lemma sub_adjoint (A B : Lℂ^n) : (A - B)† = A† - B† := by {simp}

lemma norm_sq_eq_zero (v : ℂ^n) : ∥ v ∥^2 = 0 ↔ v = 0 :=
begin
  split,
  rw ← real.sqrt_eq_zero,
  rw real.sqrt_sq,
  rw norm_eq_zero,
  intro h,
  exact h,
  exact norm_nonneg v,
  exact sq_nonneg (∥ v ∥),
  intro h,
  rw h,
  simp,
end


lemma adjoint_prod_sa : is_sa (T† * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

lemma sa_means_dag_eq_no_dag : (is_sa T) → T† = T :=
begin
  intro h,
  ext1,
  have : T† x - T x = 0 :=
  begin
    apply inner_with_all_eq_zero_eq_zero,
    intro u,

    calc ⟪ u , (T† x) - (T x) ⟫_ℂ = ⟪ u, T† x ⟫_ℂ - ⟪ u , T x ⟫_ℂ : by {rw inner_sub_right}
    ...                      = ⟪ T u, x ⟫_ℂ - ⟪ u , T x ⟫_ℂ : by {rw linear_map.adjoint_inner_right}
    ...                      = ⟪ u, T x ⟫_ℂ - ⟪ u, T x ⟫_ℂ : by {rw (h u x)}
    ...                      = 0 : by {ring},
  end,
  rw sub_eq_zero at this,
  exact this,
end


noncomputable lemma quot_by_same_is_eq {M₁ M₂ : submodule ℂ ℂ^n} (h : M₁ = M₂) : ((ℂ^n) ⧸ M₁) ≃ₗ[ℂ] ((ℂ^n) ⧸ M₂) :=
begin
  rw h,
end


lemma norm_sq_one_norm_eq_one (v : ℂ^n) : ∥ v ∥^2 = 1 → ∥ v ∥ = 1 :=
begin
  intro h,
  rw ← real.sqrt_eq_iff_sq_eq at h,
  rw ← h,
  exact real.sqrt_one,
  exact zero_le_one,
  exact norm_nonneg v,
end


lemma lin_iso_preserves_on {ι : Type} {S : submodule ℂ ℂ^n} (b : ι → S ) (h : orthonormal ℂ b) (L : S →ₗᵢ[ℂ] ℂ^n) : orthonormal ℂ (L ∘ b) :=
begin
  unfold orthonormal,
  split,
  intro i,
  apply norm_sq_one_norm_eq_one,
  apply complex.of_real_injective,
  
  calc ↑(∥(L ∘ b) i∥ ^ 2) = (∥ (L ∘ b) i ∥ : ℂ )^2 : by {simp only [complex.of_real_pow, linear_isometry_equiv.coe_to_linear_isometry, eq_self_iff_true, function.comp_app, linear_isometry_equiv.norm_map]}
    ...              = ↑∥ L (b i) ∥^2 : by {simp only [linear_isometry_equiv.coe_to_linear_isometry, eq_self_iff_true, function.comp_app, linear_isometry_equiv.norm_map]}
    ...              = ⟪ L (b i), L (b i) ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
    ...              = ⟪ b i , b i ⟫_ℂ : by {rw linear_isometry.inner_map_map}
    ...              = (∥ b i ∥^2 : ℂ) : by {rw inner_self_eq_norm_sq_to_K}
    ...              = ((1 : ℝ) : ℂ) : by {rw h.1 i, simp only [one_pow, complex.of_real_one, eq_self_iff_true]},
  intros i j hij,
  rw linear_isometry.inner_map_map,
  exact h.2 hij,
end