/-
The goal of this file is to prove the following.  If S ⊆ ℂ^n is a subspace and L : S → V is
an isometry, then there exists an isometry M : ℂ^n → ℂ^n such that M(s) = L(s) for every s ∈ S.

In other words, every isometry on a subspace of ℂ^n extends to an isometry of ℂ^n.
-/

import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (S : submodule ℂ (ℂ^n))

local attribute [instance] fact_one_le_two_real

/-
S is also a finite dimensional inner product space.
-/

noncomputable lemma hS_module : module ℂ S := by apply submodule.module

noncomputable lemma hS_ips : inner_product_space ℂ S := by apply submodule.inner_product_space

lemma hS_fd : finite_dimensional ℂ S := by apply finite_dimensional.finite_dimensional_submodule

/-
S has an orthonormal basis.
-/

noncomputable def onbasis := orthonormal_basis ℂ S

#check onbasis S

lemma hb_on : orthonormal ℂ (onbasis S) := by apply orthonormal_basis_orthonormal

/-
Let L : S → ℂ^n be an isometry.
-/

variable (L : S →ₗᵢ[ℂ] ℂ^n)

/-
Since L is an isometry, it maps the orthonormal basis to an orthonormal set.
-/

lemma hLb_on : orthonormal ℂ (L ∘ onbasis S) :=
  by apply orthonormal.comp_linear_isometry (hb_on S)

/-
Extend the basis b for S to an orthonormal basis for ℂ^n.
-/

noncomputable def b_to_S : (orthonormal_basis_index ℂ S) → S := (onbasis S)

noncomputable def b_to_Cn : (orthonormal_basis_index ℂ S) → ℂ^n := function.comp S.subtype (b_to_S S)

def b_in_Cn : set ℂ^n := set.range (b_to_Cn S)

lemma b_still_on : orthonormal ℂ (b_to_Cn S) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw b_to_Cn,
  rw b_to_S,
  rw function.comp_app,
  rw function.comp_app,
  rw submodule.subtype_apply,
  rw submodule.subtype_apply,
  rw ← submodule.coe_inner,
  revert i j,
  rw ← orthonormal_iff_ite,
  apply orthonormal_basis_orthonormal ℂ,
end

lemma b_distinct (i j : (orthonormal_basis_index ℂ S)): (i = j) ↔ ((b_to_Cn S i) = (b_to_Cn S j)) :=
begin
  split,
    intro hij,
    rw hij,
    contrapose,
    intro hij,
    have hbb : ⟪ (b_to_Cn S i), (b_to_Cn S j) ⟫_ℂ = 0 :=
    begin
      have hon : (orthonormal ℂ (b_to_Cn S)) := by apply b_still_on,
      rw orthonormal_iff_ite at hon,
      rw hon,
      rw ite_eq_right_iff,
      contrapose,
      intro dumb,
      exact hij,
    end,
    by_contradiction,
    rw h at hbb,
    have hon2 : (orthonormal ℂ (b_to_Cn S)) := by apply b_still_on,
    rw orthonormal_iff_ite at hon2,
    specialize hon2 j j,
    simp at hon2,
    simp at hbb,
    rw hon2 at hbb,
    simp only [one_ne_zero] at hbb,
    exact hbb,
end

lemma hb_still_on : orthonormal ℂ (coe : (b_in_Cn S) → ℂ^n) :=
begin
  rw orthonormal_subtype_iff_ite,
  intros v hv w hw,
  rw b_in_Cn at hv hw,
  rw set.mem_range at hv hw,
  cases hv with i hi,
  cases hw with j hj,
  rw ← hi,
  rw ← hj,
  have hon : (orthonormal ℂ (b_to_Cn S)) := by apply b_still_on,
  rw orthonormal_iff_ite at hon,
  specialize hon i j,
  rw hon,
  have hji : ¬(i = j) ↔ ¬((b_to_Cn S i) = (b_to_Cn S j)) :=
  begin
    have hij : (i = j) ↔ ((b_to_Cn S i) = (b_to_Cn S j)) := by apply b_distinct,
    cases hij with lr rl,
    split,
    contrapose,
    push_neg,
    exact rl,
    contrapose,
    push_neg,
    exact lr,
  end,
  rw ite_eq_iff,
  by_cases (i = j),
  rw b_distinct,
  left,
  rw h,
  simp only [if_true, eq_self_iff_true, and_self],
  right,
  split,
  exact h,
  rw hji at h,
  symmetry,
  rw ite_eq_right_iff,
  contrapose,
  intro dumb,
  exact h,
end

lemma extend_b_in_Cn : ∃ (u : set ℂ^n) (H : u ⊇ b_in_Cn S) (b : basis u ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
begin
  apply exists_subset_is_orthonormal_basis (hb_still_on S),
end