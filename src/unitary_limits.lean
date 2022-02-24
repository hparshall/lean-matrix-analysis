import data.complex.is_R_or_C
import topology.basic
import topology.algebra.matrix
import topology.metric_space.basic
import analysis.normed_space.basic
import linear_algebra.unitary_group
import analysis.normed_space.pi_Lp
import analysis.inner_product_space.pi_L2
import analysis.normed_space.bounded_linear_maps

variables {m n : ℕ}

open_locale big_operators complex_conjugate matrix topological_space

variables (𝕜 : Type*)
[is_R_or_C 𝕜]

local notation `𝕜^n` := (euclidean_space 𝕜 (fin n))

local notation `M_n` := (matrix (fin n) (fin n) 𝕜)

local notation `U_n` := matrix.unitary_group (fin n) 𝕜

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (euclidean_space 𝕜 (fin n)) _ x y

variables (A B : ℕ → M_n) (L : M_n)

/-
using the sup norm
-/
noncomputable instance matrix_normed_group : normed_group M_n := matrix.normed_group

noncomputable instance matrix_normed_space : normed_space 𝕜 M_n := matrix.normed_space

-- current PR
lemma norm_entry_le_entrywise_sup_norm (M : M_n) (i j : (fin n)) :
  ∥M i j∥ ≤ ∥M∥ := @le_trans _ _ _ _ _ (norm_le_pi_norm (M i) j) (norm_le_pi_norm M i)

-- uses norm_entry_le_entrywise_sup_norm
lemma entrywise_sup_norm_star_eq_norm (M : M_n) : ∥star M∥ = ∥M∥ :=
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

noncomputable instance matrix_normed_star_monoid : normed_star_monoid M_n :=
{
  norm_star := entrywise_sup_norm_star_eq_norm 𝕜
}

instance : semi_normed_ring (matrix (fin n) (fin n) 𝕜) := sorry

#check @semi_normed_ring_top_monoid M_n _

instance matrix_cont_mul := @semi_normed_ring_top_monoid M_n _

-- def matrix_continuous_mul : has_continuous_mul M_n :=
-- { continuous_mul := by { continuity,
--     simp only [matrix.mul_eq_mul, matrix.mul_apply],
--     continuity,
--     { let f := λ (x : matrix (fin n) (fin n) 𝕜 × matrix (fin n) (fin n) 𝕜), x.fst i i_2,
--       have hf1 : is_linear_map 𝕜 f :=
--       { map_add := by { intros x y,
--           simp only [f, add_left_inj, pi.add_apply, eq_self_iff_true, prod.fst_add] },
--         map_smul := by { intros x y,
--           simp only [f, algebra.id.smul_eq_mul, mul_eq_mul_left_iff, true_or, eq_self_iff_true,
--             prod.smul_fst, pi.smul_apply] }, },
--       have hf2 : is_bounded_linear_map 𝕜 f,
--       { apply is_linear_map.with_bound hf1 1,
--         simp only [f, prod.forall, one_mul],
--         intros a b,
--         have ha1 : ∥a i i_2∥ ≤ ∥a∥ := norm_entry_le_entrywise_sup_norm 𝕜 a _ _,
--         have ha2 : ∥a∥ ≤ ∥(a,b)∥ := by simp only [prod.norm_def, le_refl, true_or, le_max_iff],
--         apply @le_trans _ _ _ _ _ ha1 ha2 },
--       apply is_bounded_linear_map.continuous hf2 },
--     { let g := λ (x : matrix (fin n) (fin n) 𝕜 × matrix (fin n) (fin n) 𝕜), x.snd i_2 i_1,
--       have hg1: is_linear_map 𝕜 g :=
--       { map_add := by { intros x y,
--           simp only [g, add_left_inj, pi.add_apply, eq_self_iff_true, prod.snd_add]},
--         map_smul := by { intros x y,
--           simp only [g, algebra.id.smul_eq_mul, mul_eq_mul_left_iff, true_or, eq_self_iff_true,
--             prod.smul_snd, pi.smul_apply] }, },
--       have hg2 : is_bounded_linear_map 𝕜 g,
--       { apply is_linear_map.with_bound hg1 1,
--         simp only [g, prod.forall, one_mul],
--         intros a b,
--         have hb1 : ∥b i_2 i_1∥ ≤ ∥b∥ := norm_entry_le_entrywise_sup_norm 𝕜 b _ _,
--         have hb2 : ∥b∥ ≤ ∥(a,b)∥ := by simp only [prod.norm_def, le_refl, or_true, le_max_iff],
--         apply @le_trans _ _ (∥b i_2 i_1∥) (∥b∥) (∥(a,b)∥) hb1 hb2, },
--       apply is_bounded_linear_map.continuous hg2 },
--   },
-- }

instance matrix_proper_space : proper_space M_n := pi_proper_space

lemma entrywise_sup_norm_bound_of_unitary {U : M_n} (hU : U ∈ U_n) : ∥ U ∥ ≤ 1 :=
begin
  rw pi_norm_le_iff zero_le_one,
  intro i,
  rw pi_norm_le_iff zero_le_one,
  intro j,
  have norm_sum : ∥ U i j ∥^2 ≤ (∑ (x : (fin n)), ∥ U i x ∥^2),
  { rw fin.sum_univ_def,
    apply list.single_le_sum,
    { intros x h_x,
      rw list.mem_map at h_x,
      cases h_x with a h_a,
      rw ← h_a.2,
      norm_num },
    { rw list.mem_map,
      use j,
      simp only [ list.mem_fin_range, eq_self_iff_true, and_self, sq_eq_sq ] } },
  have norm_sum_eq_inner : ∑ (x : (fin n)), ∥ U i x ∥^2 = is_R_or_C.re ⟪U i, U i⟫,
  { simp only [ is_R_or_C.inner_apply, pi_Lp.inner_apply, finset.sum_congr, 
      is_R_or_C.conj_mul_eq_norm_sq_left, is_R_or_C.norm_sq_eq_def'],
    norm_cast },
  have inner_eq_one : is_R_or_C.re ⟪U i, U i⟫ = 1,
  { have : U ⬝ Uᴴ = 1, from unitary.mul_star_self_of_mem hU,
    simp only [ this, inner_matrix_row_row, is_R_or_C.one_re, eq_self_iff_true,
      matrix.one_apply_eq ] },
  rw ← sq_le_one_iff (norm_nonneg (U i j)),
  rw ← inner_eq_one,
  rw ← norm_sum_eq_inner,
  exact norm_sum,
end

lemma unitary_bounded : metric.bounded ((U_n) : set M_n) :=
begin
  have incl : ↑U_n ⊆ metric.ball (0 : M_n) (2) :=
  begin
    rw set.subset_def,
    intro x,
    intro h_x,
    simp only [mem_ball_zero_iff],
    have : ∥ x ∥ ≤ 1 := sorry,
    linarith,
  end,
  apply metric.bounded.mono incl,
  exact metric.bounded_ball,
end

lemma tendsto_subseq_of_unitary (A : ℕ → M_n) (hA : ∀ (i : ℕ), A i ∈ U_n):
  ∃ (L : M_n) (H : L ∈ closure (U_n : set M_n)) (φ : ℕ → ℕ), (strict_mono φ) ∧ (filter.tendsto (A ∘ φ) filter.at_top (𝓝 L)) :=
begin
  apply tendsto_subseq_of_bounded,
  exact unitary_bounded 𝕜,
  intro i,
  specialize hA i,
  exact hA,
end

lemma limit_unitary_of_unitary (h_lim : filter.tendsto B filter.at_top (𝓝 L)) (h_B : ∀ (i : ℕ), (B i) ∈ U_n) :
  L ∈ U_n :=
begin
  have h_left : filter.tendsto (star B) filter.at_top (𝓝 (star L)) :=
    by apply @filter.tendsto.star M_n _ _ _ _ B filter.at_top L h_lim,

  have tendsto_LstarL : filter.tendsto ((star B) * B) filter.at_top (𝓝 ((star L) * L)) :=
    by apply @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ h_left h_lim,

  have lim_eq_LstarL : lim (filter.at_top) ((star B) * B) = (star L) * L :=
  begin
    apply filter.tendsto.lim_eq,
    exact tendsto_LstarL,
  end,
  have tendsto_one : filter.tendsto ((star B) * B) filter.at_top (𝓝 (1)) :=
  begin
    rw filter.tendsto_def,
    intros s h,
    simp only [filter.mem_at_top_sets],
    use 0,
    intros b h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply],
    rw unitary.star_mul_self_of_mem,
    apply mem_of_mem_nhds,
    exact h,
    specialize h_B b,
    exact h_B,
  end,
  have lim_eq_one : lim (filter.at_top) ((star B) * B) = 1 :=
  begin
    apply filter.tendsto.lim_eq,
    exact tendsto_one,
  end,
  have tendsto_LLstar : filter.tendsto (B * (star B)) filter.at_top (𝓝 (L * (star L))) :=
  begin
    apply @filter.tendsto.mul _ _ _ _ _ _ _ _ _ _ h_lim h_left,
  end,
  have lim_eq_LLstar : lim (filter.at_top) (B * (star B)) = L * (star L) :=
  begin
    apply filter.tendsto.lim_eq,
    exact tendsto_LLstar,
  end,
  have tendsto_one_b : filter.tendsto (B * (star B)) filter.at_top (𝓝 (1)) :=
  begin
    rw filter.tendsto_def,
    intro s,
    intro h,
    simp only [filter.mem_at_top_sets],
    use 0,
    intro b,
    intro h_b,
    simp only [set.mem_preimage, pi.mul_apply, pi.star_apply],
    rw unitary.mul_star_self_of_mem,
    apply mem_of_mem_nhds,
    exact h,
    specialize h_B b,
    exact h_B,
  end,
  have lim_eq_one_b : lim (filter.at_top) (B * (star B)) = 1 :=
  begin
    apply filter.tendsto.lim_eq,
    exact tendsto_one_b,
  end,
  rw unitary.mem_iff,
  split,
  rw ← lim_eq_LstarL,
  exact lim_eq_one,
  rw ← lim_eq_LLstar,
  exact lim_eq_one_b,
end 


