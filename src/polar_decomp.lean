import .ladr_7_35
import .ladr_7
import .lemmas.ladr_7_lem
import linear_algebra.basic

localized "postfix `†`:1000 := linear_map.adjoint" in src
-- notation `is_sa` := inner_product_space.is_self_adjoint
variable {n : ℕ}
variable T : Lℂ^n

def is_isometry (S: Lℂ^n) : Prop := ∀ (v : ℂ^n), ∥ S v ∥ = ∥ v ∥


lemma inj_eq_surj_finite_dim (h : T.ker = ⊥) : T.range ≃ₗ[ℂ] ℂ^n :=
begin
  sorry,
end


lemma adjoint_prod_sa : is_sa (T† * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

noncomputable def sqrt' : Lℂ^n := sqrt (T† * T) (adjoint_prod_sa T)


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

lemma sqrt'_sq : ((sqrt' T) * (sqrt' T)) = T† * T :=
begin
  rw sqrt',
  rw lem_bc_1,
end

--- This is a statement about the norm-squared. Later in the proof, they use just the norm,
--- I'm hoping we can stick to norm-squared, though, since it's easier to work with Lean-wise
--- Yes, we can work with norm-squared, but that is using the lemma norm_sq_eq_zero from ladr_7_lem
-- This is the actual proof the statement, but we use it in the form eq_7_46, since it's really a statement
-- about real numbers.
lemma eq_7_46': ∀ (v : ℂ^n), (∥ T v ∥^2 : ℂ) = (∥ sqrt' T v ∥^2 : ℂ) :=
begin
  intro v,
  calc (∥ T v ∥^2 : ℂ) = ⟪ T v , T v ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
    ...          = ⟪ T† (T v), v ⟫_ℂ : by {rw linear_map.adjoint_inner_left}
    ...          = ⟪ (T† * T) v, v ⟫_ℂ : by {rw comp_eq_mul}
    ...          = ⟪ ((sqrt' T) * (sqrt' T)) v, v ⟫_ℂ : by {rw sqrt'_sq}
    ...          = ⟪ sqrt' T v, sqrt' T v ⟫_ℂ : by {rw ← comp_eq_mul, rw ← linear_map.adjoint_inner_left, rw (sa_means_dag_eq_no_dag (sqrt' T) (lem_bc_2 (T† * T) (adjoint_prod_sa T))),}
    ...          = (∥ (sqrt' T) v ∥^2 : ℂ) : by {rw inner_self_eq_norm_sq_to_K},
end

-- #check sqrt (T† * T) 

lemma eq_7_46: ∀ (v : ℂ^n), (∥ T v ∥^2 : ℝ) = (∥ sqrt' T v ∥^2 : ℝ) :=
begin
  intro v,
  apply complex.of_real_injective,
  simp,
  exact eq_7_46' T v,
end

--- The key step for S₁ being well-defined:
lemma lem_7_45_a : ∀ u v : ℂ^n, sqrt' T u = sqrt' T v → T u = T v :=
begin
  intros u v h,
  have : ∥ T u - T v ∥^2 = 0 :=
  begin
    calc ∥ T u - T v ∥^2 = ∥ T (u - v) ∥^2 : by {rw map_sub T u v}
    ...                  = ∥ sqrt' T (u - v) ∥^2 : by {rw eq_7_46}
    ...                  = ∥ (sqrt' T u) - (sqrt' T v) ∥^2 : by {rw map_sub}
    ...                  = 0 : by {rw [h, sub_self], simp},
  end,
  rw norm_sq_eq_zero at this,
  rw ← sub_eq_zero,
  exact this,
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
  sorry,
  -- rw ← linear_equiv.inv_fun_eq_symm,
  -- linear_equiv.of_injective T (linear_map.ker_eq_bot.1 inj_T),
  -- let sqr_inv_T : Lℂ^n := T * ((sqrt' T)⁻¹),
end

lemma lem_7_45'' (h : T.ker = ⊥) : ∃ (S : Lℂ^n), T = S * (sqrt' T) :=
begin
  rw ker_eq_sqrt_ker at h,
  rw linear_map.ker_eq_bot at h,
  let sqrt_T_equiv' : (ℂ^n) ≃ₗ[ℂ] (sqrt' T).range := linear_equiv.of_injective (sqrt' T) h,

  rw ← linear_map.ker_eq_bot at h,
  let sqrt_T_equiv : (ℂ^n) ≃ₗ[ℂ] (ℂ^n) := linear_equiv.trans sqrt_T_equiv' (inj_eq_surj_finite_dim (sqrt' T) h),

  use (T * sqrt_T_equiv.symm),

  sorry,
end

noncomputable def S₁ : (sqrt' T).range ≃ₗ[ℂ] T.range :=
begin
  have T_first :((ℂ^n) ⧸  T.ker) ≃ₗ[ℂ] T.range :=
  begin
    exact linear_map.quot_ker_equiv_range T,
  end,
  have Q_first :((ℂ^n) ⧸  (sqrt' T).ker) ≃ₗ[ℂ] (sqrt' T).range :=
  begin
    exact linear_map.quot_ker_equiv_range (sqrt' T),
  end,
  have same_quot : ((ℂ^n) ⧸  (sqrt' T).ker) ≃ₗ[ℂ] ((ℂ^n) ⧸  T.ker) :=
  begin
    exact submodule.quot_equiv_of_eq (sqrt' T).ker T.ker (ker_eq_sqrt_ker T).symm,
  end,
  exact (Q_first.symm).trans (same_quot.trans (T_first)),
end

#check (S₁ T).to_linear_map


-- def S₂ : T.range → (sqrt' T).range :=
-- begin
--   intro x,
--   let y : (ℂ^n) ⧸  T.ker := ((linear_map.quot_ker_equiv_range T).symm).to_linear_map x,
--   let z : (ℂ^n) ⧸ (sqrt' T).ker := y,
-- end

noncomputable lemma quot_by_same_is_eq {M₁ M₂ : submodule ℂ ℂ^n} (h : M₁ = M₂) : ((ℂ^n) ⧸ M₁) ≃ₗ[ℂ] ((ℂ^n) ⧸ M₂) :=
begin
  rw h,
end

example : ∀ v : ℂ^n, (sqrt' T).ker.mkq v = submodule.quot_equiv_of_eq T.ker (sqrt' T).ker (ker_eq_sqrt_ker T) (T.ker.mkq v) :=
begin
  intro v,
  norm_cast,
end

lemma lem_7_45_1_a (v : ℂ^n) : ((linear_map.range_restrict T) v : ℂ^n) = (linear_map.quot_ker_equiv_range T) (submodule.quotient.mk v) :=
begin
  rw linear_map.quot_ker_equiv_range_apply_mk T v,
  simp,
end

#check linear_map.quot_ker_equiv_range_apply_mk T

-- This is maybe the statement to prove?
lemma lem_7_45_1: ∀ v : ℂ^n, ((linear_map.range_restrict T v) : ℂ^n) = (S₁ T).to_linear_map ((linear_map.range_restrict (sqrt' T)) v) :=
begin
  intro v,
  rw S₁,
  simp,
  -- linear_map.quot_ker_equiv_range_apply_mk
  have : (linear_map.quot_ker_equiv_range (sqrt' T)).symm (linear_map.range_restrict (sqrt' T) v) = (sqrt' T).ker.mkq v :=
  begin
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image (sqrt' T),
    congr',
  end,
  rw this,
  simp,
end

#check ((S₁ T).to_linear_map)


lemma lem_7_45 : ∃ (S : Lℂ^n), (T = S * sqrt (T† * T) (adjoint_prod_sa T)) ∧ (is_isometry S) :=
begin
  sorry,
end


