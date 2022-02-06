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

noncomputable def f := S.subtype ∘ (onbasis S)

lemma onbasis_injective : function.injective (onbasis S) :=
begin
  apply basis.injective,
end

lemma f_injective : function.injective (f S) :=
begin
  have h_sub_inj : function.injective ⇑(S.subtype) :=
  begin
    apply subtype.coe_injective,
  end,
  apply function.injective.comp h_sub_inj (onbasis_injective S),
end

noncomputable def g := L ∘ (onbasis S)

lemma g_injective : function.injective (g S L) :=
begin
  simp only [g],
  apply function.injective.comp,
  apply linear_isometry.injective L,
  exact onbasis_injective S,
end

lemma L_to_M : ∃ (M : (ℂ^n) →ₗᵢ[ℂ] (ℂ^n)), (∀ (s : S), M s = L s) :=
begin
  let v := set.range (f S),
  have hb : ∃ (u : set ℂ^n) (H : u ⊇ v) (b : basis u ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
    by apply extend_b_in_Cn S,
  cases hb with u hb,
  cases hb with h_uv hb,
  cases hb with b_u hb,
  cases hb with hb_on hb_coe,

  let Lv := set.range (g S L),
  have hLb : ∃ (Mu : set ℂ^n) (H : Mu ⊇ Lv) (b : basis Mu ℂ ℂ^n), orthonormal ℂ b ∧ ⇑b = coe :=
    by apply extend_Lb_in_Cn S L,
  cases hLb with Mu hLb,
  cases hLb with h_MuLv hLb,
  cases hLb with b_Mu hLb,
  cases hLb with hLb_on hLb_coe,

  have h_f : ∀ (x : (orthonormal_basis_index ℂ S)), (f S x) ∈ u :=
  begin
    intro x,
    apply set.mem_of_subset_of_mem h_uv,
    apply set.mem_range_self,
  end,

  let f_to_u := set.cod_restrict (f S) u h_f,

  have fintype_u : fintype u := by apply finite_dimensional.fintype_basis_index b_u,
  have fintype_Mu : fintype Mu := by apply finite_dimensional.fintype_basis_index b_Mu,
  
  have : @fintype.card u fintype_u = @fintype.card Mu fintype_Mu :=
  begin
    rw ← @finite_dimensional.finrank_eq_card_basis _ _ _ _ _ _ fintype_u b_u,
    rw ← @finite_dimensional.finrank_eq_card_basis _ _ _ _ _ _ fintype_Mu b_Mu,
  end,

  have fintype_v : fintype v := set.fintype_range (f S),
  have fintype_Lv : fintype Lv := set.fintype_range (g S L),

  have h_cardv_S : @fintype.card v fintype_v = fintype.card (orthonormal_basis_index ℂ S) :=
  begin
    rw set.card_range_of_injective,
    exact f_injective S,
  end,

  have h_cardLv_S : @fintype.card Lv fintype_Lv = fintype.card (orthonormal_basis_index ℂ S) :=
  begin
    rw set.card_range_of_injective,
    exact g_injective S L,
  end,

  have : @fintype.card v fintype_v = @fintype.card Lv fintype_Lv :=
  begin
    rw h_cardv_S,
    rw h_cardLv_S,
  end,

  let vc := u.diff v,
  let Lvc := Mu.diff Lv,

  have fintype_vc : fintype vc := 
  begin
    apply @set.fintype_subset _ u _ fintype_u _ _,
    exact classical.dec_pred (λ (_x : ℂ^n), _x ∈ vc),
    apply set.diff_subset,
  end,

  have fintype_Lvc : fintype Lvc := 
  begin
    apply @set.fintype_subset _ Mu _ fintype_Mu _ _,
    exact classical.dec_pred (λ (_x : ℂ^n), _x ∈ Lvc),
    apply set.diff_subset,
  end,

  have h_card_vc : @fintype.card vc fintype_vc = @fintype.card Lvc fintype_Lvc := sorry,

  have h_e1 : ∃ (e1 : vc ≃ Lvc), true :=
  begin
    rw exists_true_iff_nonempty,
    rw ← @fintype.card_eq _ _ fintype_vc fintype_Lvc,
    exact h_card_vc,
  end,

  let e1 := classical.some h_e1,

  let e2 := ⇑e1,

  have h_e2 : (function.bijective e2) := equiv.bijective e1,

  have h_Lvc_inc : Lvc ⊆ set.univ := set.subset_univ Lvc,

  let e := (equiv.set.univ (ℂ^n)) ∘ (set.inclusion h_Lvc_inc) ∘ e2,

  have h_e : (function.injective e) :=
  begin
    rw equiv.comp_injective,
    apply function.injective.comp,
    exact set.inclusion_injective h_Lvc_inc,
    exact equiv.injective e1,
  end,
  
  have h_vc : vc ⊆ u := set.diff_subset u v,

  have h_e' : ∃ (e' : u → ℂ^n), ∀ (x : vc), e' ((set.inclusion h_vc x)) = e x :=
  begin
    sorry,
  end,

  let e' := classical.some h_e',

  /-
  function.extend gives a map M : u → ℂ^n where for x = f i ∈ v,
    x = f i ↦ g i = L x,
  and for x ∈ vc,
    x ↦ e x.
  e is an arbitrary bijection between u ∖ v and Mu ∖ Lv
  -/

  let M1 := function.extend f_to_u (g S L) e',

  let M2 := (basis.constr b_u ℂ) M1,

  have h_Mb_on : orthonormal ℂ (⇑M2 ∘ ⇑b_u) := sorry,

  let M := M2.isometry_of_orthonormal hb_on h_Mb_on,
  use M,
  intro s,
  simp only [M],
  rw linear_map.coe_isometry_of_orthonormal,
  rw @basis.constr_apply_fintype _ _ _ _ _ _ _ _ _ fintype_u b_u ℂ _ _ _ M1 s,
  rw basis.equiv_fun_apply,
  sorry,
end