import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import .lemmas.ladr_7_lem
import .ladr_7

variables {n : ℕ} (hn : (finite_dimensional.finrank ℂ ℂ^n) = n)

open_locale big_operators complex_conjugate matrix

notation `is_sa` := inner_product_space.is_self_adjoint

notation `Λ` := inner_product_space.is_self_adjoint.eigenvalues

def is_positive (T : Lℂ^n) :=
  (∀ v : ℂ^n, (is_R_or_C.re ⟪T v, v⟫_ℂ ≥ 0) ∧ (⟪T v, v⟫_ℂ.im = 0))

theorem thm_7_35_a_b (T : Lℂ^n) (hsa : is_sa T):
  is_positive T → ∀ (i : (fin n)), Λ hsa hn i ≥ 0 :=
begin
  sorry,
end

theorem thm_7_35_b_c (T : Lℂ^n) (hsa : is_sa T):
  (∀ (i : (fin n)), Λ hsa hn i ≥ 0)
    → ∃ (R : Lℂ^n), (R^2 = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  sorry,
end

lemma lem_gram_self_adjoint (T : Lℂ^n) :
  is_sa (T.adjoint * T) :=
begin
  sorry,
end

lemma lem_sqrt_gram (T : Lℂ^n) :
  ∃ (R : Lℂ^n), (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  apply thm_7_35_b_c,
  apply thm_7_35_a_b,
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
  simp,
  apply lem_gram_self_adjoint,
end