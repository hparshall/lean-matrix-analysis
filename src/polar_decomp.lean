import .ladr_7_35
import .ladr_7
import .lemmas.ladr_7_lem
import linear_algebra.basic

localized "postfix `†`:1000 := linear_map.adjoint" in src
variable {n : ℕ}
variable T : Lℂ^n

def is_isometry (S: Lℂ^n) : Prop := ∀ (v : ℂ^n), ∥ S v ∥ = ∥ v ∥


lemma adjoint_prod_sa : is_sa (T† * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

noncomputable def sqrt' : Lℂ^n := sqrt (T† * T) (adjoint_prod_sa T)

--- This is a statement about the norm-squared. Later in the proof, they use just the norm,
--- I'm hoping we can stick to norm-squared, though, since it's easier to work with Lean-wise
lemma eq_7_46: ∀ (v : ℂ^n), ∥ T v ∥^2 = ∥ sqrt' T v ∥^2 :=
begin
  sorry,
end

--- The key step for S₁ being well-defined:
lemma lem_7_45_a : ∀ u v : ℂ^n, sqrt' T u = sqrt' T v → T u = T v :=
begin
  sorry,
end

#check linear_map.range T

--- These definitions so that the definition of S₁ doesn't time out :/
noncomputable def range_sqrt : submodule ℂ ℂ^n := linear_map.range (sqrt' T)
noncomputable def range_T : submodule ℂ ℂ^n := linear_map.range T

--- We need to define this (which by virtue of its definition would prove that it is linear):
-- def S₁ : (range_sqrt T) →ₗ[ℂ] (range_T T) := sorry

--- I think we will need to show this (it won't be immediate from the defn):
--- Currently doesn't type check, because sqrt' T maps into C^n, and we want to land in range_sqrt, which is different


--- T and sqrt(T* T) have the same kernel
lemma ker_eq_sqrt_ker : T.ker = (sqrt' T).ker :=
begin
  ext,
  split,
  intro h,
  rw linear_map.mem_ker,
  rw linear_map.mem_ker at h,
  apply (norm_sq_eq_zero n _).1,
  calc ∥ (sqrt' T) x ∥^2 = ∥ T x ∥^2 : by {rw ← eq_7_46}
    ...                  = ∥ (0 : ℂ^n) ∥^2 : by {rw h}
    ...                  = 0 : by {rw norm_zero, ring},
  intro h,

  rw linear_map.mem_ker,
  rw linear_map.mem_ker at h,

  apply (norm_sq_eq_zero n _).1,

  calc ∥ T x ∥^2 = ∥ (sqrt' T) x ∥^2 : by {rw ← eq_7_46}
    ...                  = ∥ (0 : ℂ^n) ∥^2 : by {rw h}
    ...                  = 0 : by {rw norm_zero, ring},
end


-- def lin_equiv_sqrt_T' : (ℂ^n) ≃ₗ[ℂ] (ℂ^n) := linear_equiv ((sqrt' T))

lemma lem_7_45' (lin_equiv_sqrt_T : (ℂ^n) ≃ₗ[ℂ] (ℂ^n)) : ∃ (S : Lℂ^n), (T = S * lin_equiv_sqrt_T ) ∧ (is_isometry S) :=
begin
  let S₁ : Lℂ^n := T * lin_equiv_sqrt_T.symm,
  use T * lin_equiv_sqrt_T.symm,
  split,
  ext1,
  simp,
  -- rw ← linear_equiv.inv_fun_eq_symm,
  -- linear_equiv.of_injective T (linear_map.ker_eq_bot.1 inj_T),
  -- let sqr_inv_T : Lℂ^n := T * ((sqrt' T)⁻¹),
end



lemma lem_7_45 : ∃ (S : Lℂ^n), (T = sqrt (T† * T) (adjoint_prod_sa T)) ∧ (is_isometry S) :=
begin
  sorry,
end


