import .ladr_7_35
import .ladr_7
import .lemmas.ladr_7_lem
import linear_algebra.basic
import .gram

localized "postfix `†`:1000 := linear_map.adjoint" in src
-- notation `is_sa` := inner_product_space.is_self_adjoint
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
  rw is_positive,
  intro x,
  have : ⟪ (T† * T) x , x ⟫_ℂ = (∥ T x ∥^2 : ℂ) :=
  begin
    calc ⟪ (T† * T) x , x ⟫_ℂ = ⟪ T† (T x), x ⟫_ℂ : by {rw comp_eq_mul}
      ...                       = ⟪ T x, T x ⟫_ℂ : by {rw linear_map.adjoint_inner_left}
      ...                       = (∥ T x ∥^2 : ℂ) : by {rw inner_self_eq_norm_sq_to_K},
  end,
  rw this,
  split,
  norm_cast,
  exact pow_nonneg (norm_nonneg _) 2,
  norm_cast,
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
    ...          = ⟪ sqrt' T v, sqrt' T v ⟫_ℂ : by {rw ← comp_eq_mul, rw ← linear_map.adjoint_inner_left, rw (sa_means_dag_eq_no_dag (sqrt' T) (lem_bc_2 (T† * T) (adjoint_prod_sa T) (gram_pos T)))}-- (sqrt' T) (lem_bc_2 (T† * T) (adjoint_prod_sa T))),}
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
-- noncomputable def range_sqrt : submodule ℂ ℂ^n := linear_map.range (sqrt' T)
-- noncomputable def range_T : submodule ℂ ℂ^n := linear_map.range T

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

-- lemma lem_7_45' (lin_equiv_sqrt_T : (ℂ^n) ≃ₗ[ℂ] (ℂ^n)) : ∃ (S : Lℂ^n), (T = S * lin_equiv_sqrt_T ) ∧ (is_isometry S) :=
-- begin
--   let S₁ : Lℂ^n := T * lin_equiv_sqrt_T.symm,
--   use T * lin_equiv_sqrt_T.symm,
--   split,
--   ext1,
--   simp,
--   sorry,
--   -- rw ← linear_equiv.inv_fun_eq_symm,
--   -- linear_equiv.of_injective T (linear_map.ker_eq_bot.1 inj_T),
--   -- let sqr_inv_T : Lℂ^n := T * ((sqrt' T)⁻¹),
-- end

-- lemma lem_7_45'' (h : T.ker = ⊥) : ∃ (S : Lℂ^n), T = S * (sqrt' T) :=
-- begin
--   rw ker_eq_sqrt_ker at h,
--   rw linear_map.ker_eq_bot at h,
--   let sqrt_T_equiv' : (ℂ^n) ≃ₗ[ℂ] (sqrt' T).range := linear_equiv.of_injective (sqrt' T) h,

--   rw ← linear_map.ker_eq_bot at h,
--   let sqrt_T_equiv : (ℂ^n) ≃ₗ[ℂ] (ℂ^n) := linear_equiv.trans sqrt_T_equiv' (inj_eq_surj_finite_dim (sqrt' T) h),

--   use (T * sqrt_T_equiv.symm),

--   sorry,
-- end

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


lemma lem_7_45_1: ∀ v : ℂ^n, (T v : ℂ^n) = (S₁ T) ((linear_map.range_restrict (sqrt' T)) v) :=
begin
  intro v,
  rw S₁,
  simp,
  have : (linear_map.quot_ker_equiv_range (sqrt' T)).symm (linear_map.range_restrict (sqrt' T) v) = (sqrt' T).ker.mkq v :=
  begin
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image (sqrt' T),
    congr',
  end,
  rw this,
  simp,
end

-- We need to find some way to show this
-- It feels like the way that pullbacks happen with Lean are with sets,
-- But I don't really know how to convert to them.
lemma pullback_term (z : linear_map.range (sqrt' T)) : ∃ x : ℂ^n, z = linear_map.range_restrict(sqrt' T) x :=
begin
  -- cases (set.surjective_onto_range _ _ (sqrt' T).to_fun z) with ,
  have : ∃ x : ℂ^n, (set.range_factorization(sqrt' T)) x = z,
  begin
    apply set.surjective_onto_range,
  end,
  cases this with x hₓ,
  use x,
  rw ← hₓ,
  congr',
end


lemma S_1_preserves_norm_sq (z : linear_map.range (sqrt' T)) : ∥ (z : ℂ^n) ∥^2 = ∥ (((S₁ T) z) : ℂ^n) ∥^2  :=
begin
  cases (pullback_term T z) with x hₓ,
  rw hₓ,
  rw ← lem_7_45_1 T x,
  rw eq_7_46,
  congr',
end

lemma S_1_preserves_norm' (z : linear_map.range (sqrt' T)) : ∥ (z : ℂ^n) ∥ = ∥ (((S₁ T) z) : ℂ^n) ∥  :=
begin
  calc ∥ z ∥ = real.sqrt (∥ z ∥^2) : by {rw real.sqrt_sq (norm_nonneg z)}
  ...        = real.sqrt (∥ (((S₁ T) z) : ℂ^n) ∥^2 ) : by {rw ← S_1_preserves_norm_sq T z, congr}
  ...        = ∥ (S₁ T) z ∥ : by {rw ← real.sqrt_sq (norm_nonneg ((S₁ T) z)), congr'},

end

lemma S_1_preserves_norm (z : linear_map.range (sqrt' T)) : ∥ z ∥ = ∥ (S₁ T) z ∥ :=
begin
  calc ∥ z ∥ = ∥ (z : ℂ^n) ∥ : by {congr'}
  ...       = ∥ (((S₁ T) z) : ℂ^n) ∥ : S_1_preserves_norm' T z
  ...       = ∥ (S₁ T) z ∥ : by {congr'},
end


lemma isometry_if_preserves_norm {A B : submodule ℂ ℂ^n} (f : A →ₗ[ℂ] B) (h : ∀ z : A, ∥ z ∥ = ∥ f z ∥) : ∀ x y : A, ⟪ f x, f y ⟫_ℂ = ⟪ x , y ⟫_ℂ :=
begin
  intros x y,
  rw inner_eq_sum_norm_sq_div_four (f x) (f y),
  rw inner_eq_sum_norm_sq_div_four x y,
  simp only [is_R_or_C.I_to_complex],
  rw [← linear_map.map_smul, ← map_add, ← map_sub, ← map_add, ← map_sub],
  iterate {rw h},
end

lemma lem_7_45_2 : ∃ S₁' : linear_isometry_equiv (ring_hom.id ℂ) (sqrt' T).range T.range, ∀ v : ℂ^n,
    (S₁' ((linear_map.range_restrict (sqrt' T)) v): ℂ^n) = T v :=
  begin
    have fact_isometry : ∀ x y : (sqrt' T).range, ⟪ (S₁ T) x, (S₁ T) y ⟫_ℂ = ⟪ x , y⟫_ℂ :=
    begin
      exact isometry_if_preserves_norm ((S₁ T).to_linear_map) (S_1_preserves_norm T),
    end,
    let S₁' := linear_equiv.isometry_of_inner (S₁ T) fact_isometry,
    have : S₁'.to_linear_equiv = S₁ T :=
    begin
      rw linear_equiv.isometry_of_inner_to_linear_equiv,
    end,
    use S₁',
    intro v,
    simp only [linear_equiv.coe_isometry_of_inner],
    rw lem_7_45_1,
  end


lemma lem_7_45 : ∃ (S : Lℂ^n), (T = S * sqrt (T† * T) (adjoint_prod_sa T)) ∧ (is_isometry S) :=
begin
  sorry,
end


