import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import .lemmas.ladr_7_lem
import .ladr_7

variables {n : ℕ}

open_locale big_operators complex_conjugate matrix

notation `is_sa` := inner_product_space.is_self_adjoint

def is_positive (T : Lℂ^n) :=
  (∀ x : ℂ^n, ((is_R_or_C.re (⟪T x, x⟫_ℂ)) ≥ 0) ∧ (⟪T x, x⟫_ℂ.im = 0))

theorem thm_7_35_a_b (T : Lℂ^n) (hsa : is_sa T):
  is_positive T → (∀ (μ : ℂ), (T.has_eigenvalue μ) → (μ.re ≥ 0 ∧ μ.im = 0)) :=
begin
  intro hpos,
  intros μ hμ,
  have ev : ∃(v : ℂ^n), T.has_eigenvector μ v :=
  begin
    exact module.End.has_eigenvalue.exists_has_eigenvector hμ,
  end,
  cases ev with v hv,
  have eq : (⟪T v, v⟫_ℂ) = (conj μ) * ∥ v ∥^2 :=
  begin
    rw module.End.has_eigenvector.apply_eq_smul hv,
    rw inner_smul_left,
    rw inner_self_eq_norm_sq_to_K,
  end,
  have μ_is_real : μ.im = 0 :=
  begin
    sorry,
  end,
  have μ_is_nn : μ.re ≥ 0 :=
  begin
    sorry,
  end,
end

theorem thm_7_35_b_c (T : Lℂ^n) (hsa : is_sa T):
  (∀ (μ : ℂ), (T.has_eigenvalue μ) → (μ.re ≥ 0 ∧ μ.im = 0))
    → ∃ (R : Lℂ^n), (R^2 = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  sorry,
end

lemma lem_gram_self_adjoint (T : Lℂ^n) :
  is_sa (T.adjoint * T) :=
begin
  rw self_adjoint_iff,
  rw linear_map.eq_adjoint_iff,
  intros x y,
  have fact₀ : (T.adjoint * T) x = (linear_map.adjoint T) (T x) :=
  begin
    simp,
  end,
  have fact₁ : ⟪((T.adjoint * T) x), y⟫_ℂ = ⟪T x, T y⟫_ℂ :=
  begin
    rw fact₀,
    rw linear_map.adjoint_inner_left,
  end,
  have fact₂ : ⟪((T.adjoint * T) x), y⟫_ℂ = ⟪x, (T.adjoint * T) y⟫_ℂ :=
  begin
    rw fact₁,
    rw ← linear_map.adjoint_inner_right,
    simp,
  end,
  exact fact₂,
end

lemma lem_sqrt_gram (T : Lℂ^n) :
  ∃ (R : Lℂ^n), (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  apply thm_7_35_b_c,
  exact lem_gram_self_adjoint T,
  apply thm_7_35_a_b,
  exact lem_gram_self_adjoint T,
  rw is_positive,
  intro v,
  split,
  {
    have fact₀ : (T.adjoint * T) v = (linear_map.adjoint T) (T v) :=
    begin
      simp,
    end,
    have fact₁ : ⟪(T.adjoint * T) v, v⟫_ℂ = ⟪T v, T v⟫_ℂ :=
    begin
      rw fact₀,
      rw linear_map.adjoint_inner_left,
    end,
    rw fact₁,
    rw inner_self_eq_norm_sq,
    simp,
  },
  rw ← complex.eq_conj_iff_im,
  revert v,
  rw ← lem_7_15,
  apply lem_gram_self_adjoint,
end