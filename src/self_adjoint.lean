/-
The goal of this file is to prove that a linear operator
T : ℂ^n → ℂ^n is self-adjoint if and only if ⟪T v, v⟫_ℂ is
real for all v ∈ ℂ^n.

-- Checked over by:
-- Hans

-/

import .lemmas.ladr_7_lem

variable {n : ℕ}

localized "postfix `†`:1000 := linear_map.adjoint" in src

open_locale big_operators complex_conjugate matrix

variables (T : Lℂ^n) (u w : ℂ^n)

local notation `is_sa` := inner_product_space.is_self_adjoint

lemma is_self_adjoint_iff_eq_adjoint : is_sa T ↔ T = T† :=
  by rw [linear_map.eq_adjoint_iff, inner_product_space.is_self_adjoint]

/-
Linearity lemmas
-/
lemma inner_map_add_add : ⟪ T (u + w), u + w ⟫_ℂ = ⟪T u, u⟫_ℂ + ⟪T w, u⟫_ℂ + ⟪T u, w⟫_ℂ + ⟪T w, w⟫_ℂ :=
  by {rw [map_add, inner_add_left, inner_add_right, inner_add_right], ring}

lemma inner_map_sub_sub : ⟪ T (u - w), u - w ⟫_ℂ = ⟪T u, u⟫_ℂ - ⟪T w, u⟫_ℂ - ⟪T u, w⟫_ℂ + ⟪T w, w⟫_ℂ :=
  by {rw [map_sub,inner_sub_left, inner_sub_right, inner_sub_right], ring}

/-
Polarization identity 
-/
lemma inner_map_polarization :
  4 * ⟪ T w, u ⟫_ℂ = ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ :=
begin
  symmetry,
  iterate {rw inner_map_add_add},
  iterate {rw inner_map_sub_sub},
  rw [linear_map.map_smul, inner_smul_left, inner_smul_right],
  ring_nf,
  rw complex.conj_I,
  ring_nf,
  rw complex.I_sq,
  ring_nf,
end

/-
If ⟪T u, u⟫_ℂ = 0 for all u ∈ ℂ^n, then ⟪T u, w⟫_ℂ = 0 for all u, w ∈ ℂ^n.
-/
lemma inner_map_eq_zero (h : ∀ (u : ℂ^n), ⟪T u, u⟫_ℂ = 0) : 
  ∀ (u w : ℂ^n), ⟪T u, w ⟫_ℂ = 0 :=
begin
  have : ∀ u w : ℂ^n, 4 * ⟪T u, w ⟫_ℂ = 0 :=
  begin
    intros u w,
    rw inner_map_polarization,
    iterate {rw h},
    ring,
  end,
  intros u w,
  specialize this u w,
  simp only [false_or, bit0_eq_zero, one_ne_zero, mul_eq_zero] at this,
  exact this,
end 

/-
If ⟪T u, u⟫_ℂ = 0 for all u ∈ ℂ^n, then ⟪T u, w⟫_ℂ = 0 for all u, w ∈ ℂ^n.
-/
lemma inner_map_self_eq_zero (h : ∀ u : ℂ^n, ⟪T u, u⟫_ℂ = 0) :
  T = 0 :=
begin
  have : ∀ u w : ℂ^n, ⟪T u, w ⟫_ℂ = 0 := inner_map_eq_zero T h,
  apply linear_map.ext,
  intro x,
  specialize this x (T x),
  rw inner_self_eq_zero at this,
  rw linear_map.zero_apply,
  exact this,
end

/-
If T is self-adjoint, then ⟪T v, v⟫_ℂ is real for all v ∈ ℂ
-/
lemma self_adjoint_real_inner (h : is_sa T) : 
  ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
begin
  intro v,
  apply inner_product_space.is_self_adjoint.conj_inner_sym,
  exact h,
end

/-
If ⟪T v, v⟫_ℂ is real for all v ∈ ℂ^n, then T is self-adjoint.
-/
lemma real_inner_self_adjoint (h : ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ) :
  is_sa T :=
begin
  rw is_self_adjoint_iff_eq_adjoint,
  rw ← sub_eq_zero,
  apply inner_map_self_eq_zero,
  intro v,
  specialize h v,
  rw linear_map.sub_apply,
  rw inner_sub_left,
  rw linear_map.adjoint_inner_left,
  rw ← h,
  rw inner_conj_sym,
  rw sub_self,
end

/-
T is self-adjoint if and only if ⟪T v, v⟫_ℂ
-/
lemma is_self_adjoint_iff_real_inner_map : (is_sa T) ↔ ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
begin
  split,
  intro h,
  apply self_adjoint_real_inner T h,
  intro h,
  apply real_inner_self_adjoint T h,
end