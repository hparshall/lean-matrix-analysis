import data.complex.is_R_or_C
import topology.basic
import topology.algebra.matrix
import analysis.normed_space.basic
import linear_algebra.unitary_group
import analysis.normed_space.pi_Lp

variables {m n : ℕ}

open_locale topological_space

variables (𝕜 : Type*)
[is_R_or_C 𝕜]

local notation `M_n` := (matrix (fin n) (fin n) 𝕜)

noncomputable instance frob_normed_group : normed_group M_n :=
  pi_Lp.normed_group 2 _

noncomputable instance frob_semi_normed_group : semi_normed_group M_n :=
  pi_Lp.semi_normed_group 2 _

noncomputable instance frob_normed_space : normed_space 𝕜 M_n :=
  pi_Lp.normed_space 2 _ 𝕜
  
variables (A : ℕ → M_n) (L : M_n)

/-
Aᵢ → L if and only if ∥Aᵢ - L∥ → 0.
-/
example : filter.tendsto A filter.at_top (𝓝 L) ↔ filter.tendsto (λ (i : ℕ), ∥(A i) - L∥) filter.at_top (𝓝 0) :=
  tendsto_iff_norm_tendsto_zero

local notation `U_n` := matrix.unitary_group (fin n) 𝕜

variables (B : ℕ → M_n)

instance Un_t2_space  : t2_space M_n := sorry

lemma matrix_unitary_seq_compact : seq_compact_space U_n := sorry

instance matrix_continuous_mul : has_continuous_mul M_n := sorry

instance matrix_normed_star_monoid : normed_star_monoid M_n := sorry

example (h_lim : filter.tendsto B filter.at_top (𝓝 L)) (h_B : ∀ (i : ℕ), (B i) ∈ U_n) :
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


