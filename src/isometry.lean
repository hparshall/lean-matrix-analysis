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
import .linear_independent

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (S : submodule ℂ (ℂ^n))

local attribute [instance] fact_one_le_two_real

/-
S is also a finite dimensional inner product space.
-/

noncomputable lemma hS_module : module ℂ S := submodule.module S

noncomputable lemma hS_ips : inner_product_space ℂ S := submodule.inner_product_space S

lemma hS_fd : finite_dimensional ℂ S := finite_dimensional.finite_dimensional_submodule S

/-
S has an orthonormal basis.
-/

noncomputable def onbasis := orthonormal_basis ℂ S

lemma hb_on : orthonormal ℂ (onbasis S) := orthonormal_basis_orthonormal ℂ S

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

lemma b_distinct (i j : (orthonormal_basis_index ℂ S)): (b_to_Cn S i) = (b_to_Cn S j) ↔ i = j :=
  linear_independent_distinct (b_still_on S).linear_independent

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
    have hij : ((b_to_Cn S i) = (b_to_Cn S j)) ↔ (i = j) := by apply b_distinct,
    cases hij with lr rl,
    split,
    contrapose,
    push_neg,
    exact lr,
    contrapose,
    push_neg,
    exact rl,
  end,
  rw ite_eq_iff,
  by_cases (i = j),
  rw ← b_distinct,
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
  exists_subset_is_orthonormal_basis (hb_still_on S)

/-
Let L : S → ℂ^n be an isometry.
-/

variable (L : S →ₗᵢ[ℂ] ℂ^n)

/-
Since L is an isometry, it maps the orthonormal basis to an orthonormal set.
-/

lemma hLb_on : orthonormal ℂ (L ∘ onbasis S) := (hb_on S).comp_linear_isometry L

/-
Extend the image of the orthonormal basis to an orthonormal basis.
-/

lemma Lb_distinct (i j : (orthonormal_basis_index ℂ S)): (L ∘ onbasis S) i = (L ∘ onbasis S) j ↔ i = j :=
  linear_independent_distinct (hLb_on S L).linear_independent

lemma hLb_still_on : orthonormal ℂ (coe : set.range (L ∘ onbasis S) → ℂ^n) :=
begin
  rw orthonormal_subtype_iff_ite,
  intros v hv w hw,
  rw set.mem_range at hv hw,
  cases hv with i hi,
  cases hw with j hj,
  have hon : orthonormal ℂ (L ∘ onbasis S) := by apply hLb_on,
  have hvw : ⟪v, w⟫_ℂ = ite (i = j) 1 0 :=
  begin
    rw ← hi,
    rw ← hj,
    rw orthonormal_iff_ite at hon,
    specialize hon i j,
    exact hon,
  end,
  rw hvw,
  have hij : ¬i = j → ¬v = w :=
  begin
    contrapose,
    push_neg,
    rw ← hi,
    rw ← hj,
    intro h,
    rw Lb_distinct at h,
    exact h,
  end,
  by_cases i = j,
  rw ← hi,
  rw ← hj,
  rw h,
  simp only [if_true, eq_self_iff_true, function.comp_app, linear_isometry.map_eq_iff],
  have hl : @ite ℂ (i = j) _ 1 0 = 0 :=
  begin
    rw ne.ite_eq_right_iff,
    exact h,
    simp only [ne.def, not_false_iff, one_ne_zero],
  end,
  have hr : @ite ℂ (v = w) _ 1 0 = 0 :=
  begin
    rw ne.ite_eq_right_iff,
    apply hij,
    exact h,
    simp only [ne.def, not_false_iff, one_ne_zero],
  end,
  rw hl,
  rw hr,
end

lemma extend_Lb_in_Cn : ∃ (u : set ℂ^n) (H : u ⊇ set.range (L ∘ onbasis S)) (b : basis u ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
  exists_subset_is_orthonormal_basis (hLb_still_on S L)

--- will need M an isometry
-- lemma L_to_M : ∃ (M : ((ℂ^n) → ℂ^n)), ∀ (s : S), M s = L s :=
-- begin
--   let v := b_in_Cn S,
--   have hb : ∃ (u : set ℂ^n) (H : u ⊇ v) (b : basis u ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
--     by apply extend_b_in_Cn S,
--   cases hb with u hb,
--   cases hb with h_uv hb,
--   cases hb with b_u hb,
--   cases hb with hb_on hb_coe,
--   let Lv := set.range (L ∘ onbasis S),
--   have hLb : ∃ (Mu : set ℂ^n) (H : Mu ⊇ Lv) (b : basis Mu ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
--     by apply extend_Lb_in_Cn S L,
--   cases hLb with Mu hLb,
--   cases hLb with h_MuLv hLb,
--   cases hLb with b_Mu hLb,
--   cases hLb with hLb_on hLb_coe,

--   have fintype_u : fintype u :=
--   begin
--     apply basis.fintype_index_of_dim_lt_omega b_u,
--     rw ← finite_dimensional.finrank_eq_dim,
--     simp only [fintype.card_fin, finrank_euclidean_space],
--     apply cardinal.nat_lt_omega,
--   end,

--   have finset_u : finset u := @finset.univ _ fintype_u,

--   have fintype_Mu : fintype Mu :=
--   begin
--     apply basis.fintype_index_of_dim_lt_omega b_Mu,
--     rw ← finite_dimensional.finrank_eq_dim,
--     simp only [fintype.card_fin, finrank_euclidean_space],
--     apply cardinal.nat_lt_omega,
--   end,

--   have finset_Mu : finset Mu := @finset.univ _ fintype_Mu,

--   have fintype_v : fintype (set.range (onbasis S)) := sorry,

--   have fintype_Lv : fintype Lv := sorry,

--   -- need to restrict codomain too
--   let v_to_Lv :=
--     set.cod_restrict (set.restrict L (set.range (onbasis S))) (Lv),

--   have v_to_Lv_bij : function.bijective v_to_Lv := sorry,

--   have : @fintype.card (set.range (onbasis S)) fintype_v = 
--     @fintype.card Lv fintype_Lv :=
--   begin
--     apply fintype.card_of_bijective v_to_Lv_bij,
    
--   end,
  
  

--   sorry,
-- end

