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