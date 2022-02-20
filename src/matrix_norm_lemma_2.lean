import analysis.normed_space.basic
import data.complex.is_R_or_C


variables {m n : ℕ} {α : Type*} [is_R_or_C α]

open_locale complex_conjugate matrix

local attribute [instance] matrix.normed_group

/- here for convenience, do not load into mathlib again! -/
lemma norm_entry_le_entrywise_sup_norm (M : matrix (fin m) (fin n) α) (i : (fin m)) (j : (fin n)) :
  ∥M i j∥ ≤ ∥M∥ := @le_trans _ _ _ _ _ (norm_le_pi_norm (M i) j) (norm_le_pi_norm M i)

lemma entrywise_sup_norm_star_eq_norm (M : matrix (fin n) (fin n) α) : ∥star M∥ = ∥M∥ :=
begin
  have star_le : ∥star M∥ ≤ ∥M∥ :=
  begin
    rw [matrix.star_eq_conj_transpose, norm_matrix_le_iff (norm_nonneg M)],
    intros i j,
    simp only [matrix.conj_transpose_apply, normed_star_monoid.norm_star],
    apply norm_entry_le_entrywise_sup_norm,
  end,
  have no_star_le : ∥M∥ ≤ ∥star M∥ :=
  begin
    rw matrix.star_eq_conj_transpose,
    rw norm_matrix_le_iff (norm_nonneg Mᴴ),
    intros i j,
    have : ∥M i j∥ = ∥Mᴴ j i∥ :=
      by simp only [matrix.conj_transpose_apply, eq_self_iff_true,normed_star_monoid.norm_star],
    rw this,
    apply norm_entry_le_entrywise_sup_norm,
  end,
  exact ge_antisymm no_star_le star_le,
end

noncomputable def matrix_normed_star_monoid : normed_star_monoid (matrix (fin n) (fin n) α) :=
{
  norm_star := entrywise_sup_norm_star_eq_norm
}