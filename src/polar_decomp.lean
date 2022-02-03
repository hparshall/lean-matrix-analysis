import .ladr_7_35
import .ladr_7
import .lemmas.ladr_7_lem
import linear_algebra.basic
import .gram

localized "postfix `†`:1000 := linear_map.adjoint" in src
variable {n : ℕ}
variable T : Lℂ^n

noncomputable def sqrt' (T : Lℂ^n) : Lℂ^n := classical.some (sqrt_gram T)

local notation `R` := (sqrt' T)

lemma R_sa : is_sa R :=
begin
  have : (R^2 = T† * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram T),
  exact this.2.1,
end

lemma R_mul_mul : R * R = T† * T :=
begin
  have : (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram T),
  exact this.1,
end

lemma R_pos : is_positive R :=
begin
  have : (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) := classical.some_spec (sqrt_gram T),
  exact this.2.2,
end

-- This is the actual proof the statement, but we use it in the form eq_7_46, since it's really a statement
-- about real numbers.
lemma eq_7_46': ∀ (v : ℂ^n), (∥ T v ∥^2 : ℂ) = (∥ R v ∥^2 : ℂ) :=
begin
  intro v,
  calc (∥ T v ∥^2 : ℂ) = ⟪ T v , T v ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
    ...          = ⟪ T† (T v), v ⟫_ℂ : by {rw linear_map.adjoint_inner_left}
    ...          = ⟪ (T† * T) v, v ⟫_ℂ : by {rw comp_eq_mul}
    ...          = ⟪ (R * R) v, v ⟫_ℂ : by {rw R_mul_mul}
    ...          = ⟪ R v, R v ⟫_ℂ : by {rw ← comp_eq_mul, rw ← linear_map.adjoint_inner_left, rw sa_means_dag_eq_no_dag (R_sa T)}
    ...          = (∥ R v ∥^2 : ℂ) : by {rw inner_self_eq_norm_sq_to_K},
end
-- The actual statement about norms as real numbers:
lemma eq_7_46: ∀ (v : ℂ^n), (∥ T v ∥^2 : ℝ) = (∥ R v ∥^2 : ℝ) :=
begin
  intro v,
  apply complex.of_real_injective,
  simp,
  exact eq_7_46' T v,
end

lemma ker_eq_sqrt_ker : T.ker = (R).ker :=
begin
  ext,
  split,
  intro h,
  rw linear_map.mem_ker,
  rw linear_map.mem_ker at h,
  apply (norm_sq_eq_zero _).1,
  calc ∥ (sqrt' T) x ∥^2 = ∥ T x ∥^2 : by {rw ← eq_7_46}
    ...                  = ∥ (0 : ℂ^n) ∥^2 : by {rw h}
    ...                  = 0 : by {rw norm_zero, ring},
  intro h,

  rw linear_map.mem_ker,
  rw linear_map.mem_ker at h,

  apply (norm_sq_eq_zero _).1,

  calc ∥ T x ∥^2 = ∥ R x ∥^2 : by {rw ← eq_7_46}
    ...                  = ∥ (0 : ℂ^n) ∥^2 : by {rw h}
    ...                  = 0 : by {rw norm_zero, ring},
end

-- We define the isometry by
-- 1. pulling back the range of R to the domain / kernel of R,
-- 2. identifying the kernels of R and T
-- 3. pushing forward from the domain / kernel of T to range T
noncomputable def S₁ : (R).range ≃ₗ[ℂ] T.range :=
begin
  have T_first :((ℂ^n) ⧸  T.ker) ≃ₗ[ℂ] T.range :=
  begin
    exact linear_map.quot_ker_equiv_range T,
  end,
  have Q_first :((ℂ^n) ⧸  (R).ker) ≃ₗ[ℂ] (R).range :=
  begin
    exact linear_map.quot_ker_equiv_range R,
  end,
  have same_quot : ((ℂ^n) ⧸  (R).ker) ≃ₗ[ℂ] ((ℂ^n) ⧸  T.ker) :=
  begin
    exact submodule.quot_equiv_of_eq (R).ker T.ker (ker_eq_sqrt_ker T).symm,
  end,
  exact (Q_first.symm).trans (same_quot.trans (T_first)),
end


lemma lem_7_45_1: ∀ v : ℂ^n, (T v : ℂ^n) = (S₁ T) ((linear_map.range_restrict R) v) :=
begin
  intro v,
  rw S₁,
  simp,
  have : (linear_map.quot_ker_equiv_range R).symm (linear_map.range_restrict R v) = (R).ker.mkq v :=
  begin
    rw ← linear_map.quot_ker_equiv_range_symm_apply_image R,
    congr',
  end,
  rw this,
  simp,
end

-- Presumably there's a thing in mathlib to do this already, but I haven't been able to find it
lemma pullback_term (z : linear_map.range R) : ∃ x : ℂ^n, z = linear_map.range_restrict (R) x :=
begin
  have : ∃ x : ℂ^n, (set.range_factorization R) x = z,
  begin
    apply set.surjective_onto_range,
  end,
  cases this with x hₓ,
  use x,
  rw ← hₓ,
  congr',
end


lemma S_1_preserves_norm_sq (z : linear_map.range R) : ∥ (z : ℂ^n) ∥^2 = ∥ (((S₁ T) z) : ℂ^n) ∥^2  :=
begin
  cases (pullback_term T z) with x hₓ,
  rw hₓ,
  rw ← lem_7_45_1 T x,
  rw eq_7_46,
  congr',
end

lemma S_1_preserves_norm' (z : linear_map.range R) : ∥ (z : ℂ^n) ∥ = ∥ (((S₁ T) z) : ℂ^n) ∥  :=
begin
  calc ∥ z ∥ = real.sqrt (∥ z ∥^2) : by {rw real.sqrt_sq (norm_nonneg z)}
  ...        = real.sqrt (∥ (((S₁ T) z) : ℂ^n) ∥^2 ) : by {rw ← S_1_preserves_norm_sq T z, congr}
  ...        = ∥ (S₁ T) z ∥ : by {rw ← real.sqrt_sq (norm_nonneg ((S₁ T) z)), congr'},

end

lemma S_1_preserves_norm (z : linear_map.range R) : ∥ z ∥ = ∥ (S₁ T) z ∥ :=
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

lemma lem_7_45_2 : ∃ S₁' : linear_isometry_equiv (ring_hom.id ℂ) (R).range T.range, ∀ v : ℂ^n,
    (S₁' ((linear_map.range_restrict R) v): ℂ^n) = T v :=
  begin
    have fact_isometry : ∀ x y : (R).range, ⟪ (S₁ T) x, (S₁ T) y ⟫_ℂ = ⟪ x , y⟫_ℂ :=
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


lemma lem_7_45 : ∃ (S : linear_isometry_equiv (ring_hom.id ℂ) (ℂ^n) (ℂ^n)), ∀ v : ℂ^n, (T v = S (R v)) :=
begin
  sorry,
end


