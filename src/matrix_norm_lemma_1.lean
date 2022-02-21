import analysis.normed_space.basic
import data.complex.is_R_or_C


variables {m n : ℕ} {α : Type*} [normed_ring α]

open_locale complex_conjugate matrix

local attribute [instance] matrix.normed_group

lemma norm_entry_le_entrywise_sup_norm (M : matrix (fin m) (fin n) α) (i : (fin m)) (j : (fin n)) :
  ∥M i j∥ ≤ ∥M∥ := @le_trans _ _ _ _ _ (norm_le_pi_norm (M i) j) (norm_le_pi_norm M i)