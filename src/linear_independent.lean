import linear_algebra.linear_independent

variables {ι : Type*} {R : Type*} {M : Type*} {v : ι → M} {i j : ι}
[ring R] [add_comm_group M] [nontrivial R] [module R M] [fintype ι] [decidable_eq ι]

open_locale big_operators

lemma linear_independent_distinct (hli : (linear_independent R v)) : v i = v j ↔ i = j :=
begin
  split,
  {
    contrapose,
    intro hij,
    by_contradiction,
    rw fintype.linear_independent_iff at hli,
    let g : (ι → R) := λ (x : ι), (( ite (x = i) 1 0 ) - ( ite (x = j) 1 0 )),
    specialize hli g,
    let f : (ι → M) := λ (x : ι), g x • v x,
    have hgsum : ∑ (x : ι), g x • v x = ∑ (x : ι), f x := by simp only [f],
    have hfsum : ∑ (x : ι), f x = f i + f j :=
    begin
      apply fintype.sum_eq_add,
      exact hij,
      intros x hx,
      simp only [f],
      simp only [g],
      cases hx with hxi hxj,
      have : ite (x = i) (1 : R) (0 : R) = 0 :=
      begin
        rw ne.ite_eq_right_iff,
        exact hxi,
        simp only [ne.def, not_false_iff, one_ne_zero],
      end,
      rw this,
      have : ite (x = j) (1 : R) (0 : R) = 0 :=
      begin
        rw ne.ite_eq_right_iff,
        exact hxj,
        simp only [ne.def, not_false_iff, one_ne_zero],
      end,
      rw this,
      simp only [eq_self_iff_true, sub_zero, zero_smul],
    end,
    have hz : ∀ (x : ι), g x = 0 :=
    begin
      apply hli,
      rw hgsum,
      rw hfsum,
      simp only [f],
      simp only [g],
      simp,
      have : ite (i = j) (1 : R) (0 : R) = 0 :=
      begin
        rw ne.ite_eq_right_iff,
        exact hij,
        simp only [ne.def, not_false_iff, one_ne_zero],
      end,
      rw this,
      have : ite (j = i) (1 : R) (0 : R) = 0 :=
      begin
        rw ne.ite_eq_right_iff,
        apply ne.symm,
        exact hij,
        simp only [ne.def, not_false_iff, one_ne_zero],
      end,
      rw this,
      simp,
      rw add_eq_zero_iff_eq_neg,
      simp,
      exact h,
    end,
    specialize hz i,
    simp only [g] at hz,
    simp only [if_true, eq_self_iff_true] at hz,
    have hne : ite (i = j) (1 : R) (0 : R) = 0 :=
    begin
      rw ne.ite_eq_right_iff,
      exact hij,
      exact one_ne_zero,
    end,
    rw hne at hz,
    simp only [sub_zero, one_ne_zero] at hz,
    exact hz,
  },
  tauto,
end


lemma inside_eq₁ (i j : ι) : finset.filter(λ a : ι, ((a = i) ∨ (a = j)) ∧ (a = i)) finset.univ = finset.filter(λ a : ι, a = i) finset.univ :=
begin
  ext,
  split,
  intro h,
  simp at h,
  simp,
  exact h.2,
  intro h,
  simp at h,
  simp,
  split,
  left,
  exact h,
  exact h,
end

lemma inside_eq₂ (i j : ι) (H : ¬(i = j)) : finset.filter(λ a : ι, ((a = i) ∨ (a = j)) ∧ (¬a = i)) finset.univ = finset.filter(λ a : ι, a = j) finset.univ :=
begin
  ext,
  split,
  intro h,
  simp at h,
  simp,
  rw or_and_distrib_right at h,
  simp at h,
  exact h.1,
  intro h,
  simp at h,
  simp,
  split,
  right,
  exact h,
  rw ← h at H,
  intro fals,
  rw fals at H,
  exact H rfl,
end

lemma linear_independent_distinct' (hli : (linear_independent R v)) : v i = v j ↔ i = j :=
begin
  rw fintype.linear_independent_iff at hli,
  split,
  intro hij,
  by_contradiction,
  let g := λ x, ite (x = i ∨ x = j) (ite (x = i) (1 : R) (-1 : R)) (0 : R),
  specialize hli g,
  simp at hli,
  apply hli,
  simp only [g],
  calc ∑ (x : ι), ite (x = i ∨ x = j) (ite (x = i) (1 : R) (-1 : R)) 0 • v x = ∑ (x : ι), ite (x = i ∨ x = j) (ite (x = i) (v x) (-(v x))) (0 : M): by {
    conv
    {
      to_lhs,
      congr,
      skip,
      funext,
      rw ite_smul,
      rw ite_smul,
    },
    simp,
  }
    ...                = ∑ (x : ι) in finset.filter (λ x, x = i ∨ x = j) finset.univ, ite (x = i) (v x) (-(v x)) : by {rw finset.sum_ite, rw finset.sum_const_zero, simp}
    ...                = v i - (v j) : by {rw finset.sum_ite, rw finset.filter_filter, rw finset.filter_filter, rw inside_eq₁, rw inside_eq₂ _ _ h, rw finset.sum_eq_single_of_mem i, rw finset.sum_eq_single_of_mem j, rw sub_eq_add_neg, simp,
      intros b h₁ h₂,
      simp at h₁,
      contradiction,
      simp,
      intros b h₁ h₂,
      simp at h₁,
      contradiction
    }
    ...                = 0 : by {rw hij, rw sub_self},
  intro h,
  rw h,
end


-- lemma two_elem_filter (i j : ι) : finset.filter (λ x : ι, x = i ∨ x = j) finset.univ = {i, j} :=
-- begin
--   ext,
--   split,
--   intro h,
--   have : (a = i) ∨ (a = j) :=
--   begin
--     rw finset.mem_filter at h,
--     exact h.2,
--   end,
--   cases this,
--   rw this,
--   simp only [true_or, eq_self_iff_true, finset.mem_insert, finset.mem_singleton],
--   rw this,
--   simp only [eq_self_iff_true, or_true, finset.mem_insert, finset.mem_singleton],
--   intro h,
--   rw finset.mem_filter,
--   split,
--   exact finset.mem_univ a,
--   sorry,
  
-- end