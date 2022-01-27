import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem
import .ladr_7

variables {n : ℕ}

open_locale big_operators complex_conjugate matrix

notation `is_sa` := inner_product_space.is_self_adjoint

lemma hn : finite_dimensional.finrank ℂ (ℂ^n) = n := by simp

noncomputable def e_vals (T : Lℂ^n) (hsa : is_sa T):=
  inner_product_space.is_self_adjoint.eigenvalues hsa hn

noncomputable def e_vecs (T : Lℂ^n) (hsa : is_sa T) :=
  @inner_product_space.is_self_adjoint.eigenvector_basis ℂ _ _ (ℂ^n) _ T hsa _ n hn

noncomputable def scaled_e_vecs (T : Lℂ^n) (hsa : is_sa T) (b : (basis (fin n) ℂ ℂ^n)):
  (fin n) → ℂ^n :=
  λ (i : (fin n)), real.sqrt(((e_vals T hsa) i)) • (b i)

noncomputable def sqrt (T : Lℂ^n) (hsa : is_sa T) : Lℂ^n :=
  @basis.constr (fin n) ℂ (ℂ^n) (ℂ^n) _ _ _ _ _ (e_vecs T hsa) ℂ _ _ _ (scaled_e_vecs T hsa (e_vecs T hsa))

def is_positive (T : Lℂ^n) :=
  (∀ x : ℂ^n, (⟪T x, x⟫_ℂ.re ≥ 0) ∧ (⟪T x, x⟫_ℂ.im = 0))

theorem thm_7_35_a_b (T : Lℂ^n) (hsa : is_sa T):
  is_positive T → (∀ (μ : ℂ), (T.has_eigenvalue μ) → (μ.re ≥ 0 ∧ μ.im = 0)) :=
begin
  intro hpos,
  intros μ hμ,
  have ev : ∃(v : ℂ^n), T.has_eigenvector μ v :=
    by exact module.End.has_eigenvalue.exists_has_eigenvector hμ,
  cases ev with v hv,
  have eq : (⟪T v, v⟫_ℂ) = (conj μ) * ∥ v ∥^2 :=
  begin
    rw module.End.has_eigenvector.apply_eq_smul hv,
    rw inner_smul_left,
    rw inner_self_eq_norm_sq_to_K,
  end,
  rw complex.ext_iff at eq,
  cases eq with hre him,
  rw is_positive at hpos,
  specialize hpos v,
  cases hpos with hnn himz,
  rw himz at him,
  rw complex.mul_im at him,
  norm_cast at him,
  simp at him,
  rw module.End.has_eigenvector at hv,
  have muim : μ.im = 0 := by tauto,
  split,
  rw hre at hnn,
  norm_cast at hnn,
  rw complex.mul_re at hnn,
  norm_cast at hnn,
  simp at hnn,
  rw ← div_le_iff at hnn,
  simp at hnn,
  norm_cast,
  exact hnn,
  cases hv with eig nz,
  rw ← real.sqrt_ne_zero',
  simp,
  simp at nz,
  exact nz,
  exact muim,
end

theorem thm_7_35_b_c (T : Lℂ^n) (hsa : is_sa T):
  (∀ (μ : ℂ), (T.has_eigenvalue μ) → (μ.re ≥ 0 ∧ μ.im = 0))
    → ∃ (R : Lℂ^n), (R^2 = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  intro h,
  use (sqrt T hsa),
  split,
  apply basis.ext (e_vecs T hsa),
  intro i,
  simp,
  let vi := (e_vecs T hsa) i,
  let μi := (e_vals T hsa) i,
  have fact₁ : T vi = μi • vi :=
  begin
    sorry,
  end,
  have fact₂ : (sqrt T hsa) vi = (real.sqrt μi) • vi :=
  begin
    sorry,
  end,
  rw fact₁,
  rw fact₂,
  have fact₃ : (sqrt T hsa) (real.sqrt μi • vi) = (real.sqrt μi) • ((sqrt T hsa) vi) :=
  begin
    simp,
  end,
  rw fact₃,
  rw fact₂,
  rw smul_smul,
  have fact₄ : real.sqrt μi * real.sqrt μi = μi :=
  begin
    sorry,
  end,
  rw fact₄,
  sorry,
end

lemma lem_gram_self_adjoint (T : Lℂ^n) :
  is_sa (T.adjoint * T) :=
begin
  rw self_adjoint_iff,
  rw linear_map.eq_adjoint_iff,
  intros x y,
  have fact₁ : ⟪((T.adjoint * T) x), y⟫_ℂ = ⟪T x, T y⟫_ℂ :=
  begin
    rw ← comp_eq_mul,
    rw linear_map.adjoint_inner_left,
  end,
  have fact₂ : ⟪((T.adjoint * T) x), y⟫_ℂ = ⟪x, (T.adjoint * T) y⟫_ℂ :=
  begin
    rw fact₁,
    rw ← linear_map.adjoint_inner_right,
    rw comp_eq_mul,
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
    have fact₁ : ⟪(T.adjoint * T) v, v⟫_ℂ = ⟪T v, T v⟫_ℂ :=
    begin
      rw ← comp_eq_mul,
      rw linear_map.adjoint_inner_left,
    end,
    rw fact₁,
    norm_cast,
    have fact₂ : ⟪T v,T v⟫_ℂ.re = is_R_or_C.re ⟪T v,T v⟫_ℂ :=
    begin
      simp,
    end,
    rw fact₂,
    apply inner_self_nonneg,
  },
  rw ← complex.eq_conj_iff_im,
  revert v,
  rw ← lem_7_15,
  apply lem_gram_self_adjoint,
end