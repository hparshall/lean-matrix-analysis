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