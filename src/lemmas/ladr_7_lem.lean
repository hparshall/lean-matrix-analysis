import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp

variable n : ℕ
def C : Type := euclidean_space ℂ (fin n)

notation `C` n := euclidean_space ℂ (fin n)
notation `ℂ^` n := euclidean_space ℂ (fin n)
notation `Lℂ^` n := module.End ℂ ℂ^n

notation `I` := complex.I

localized "postfix `†`:1000 := linear_map.adjoint" in src

variable T : module.End ℂ ℂ^n

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

lemma mul_adjoint (A B : Lℂ^n) : (A * B)† = B† * A† := adjoint_prod n A B

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