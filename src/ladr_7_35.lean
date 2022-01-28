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

variables (T : Lℂ^n) (hsa : is_sa T)

noncomputable def e_vals : (fin n → ℝ) :=
  inner_product_space.is_self_adjoint.eigenvalues hsa hn

noncomputable def e_vecs : (basis (fin n) ℂ (ℂ^n)) :=
  @inner_product_space.is_self_adjoint.eigenvector_basis ℂ _ _ (ℂ^n) _ T hsa _ n hn

noncomputable def scaled_e_vecs : (fin n) → ℂ^n :=
  λ (i : (fin n)), real.sqrt(((e_vals T hsa) i)) • ((e_vecs T hsa) i)

noncomputable def sqrt (T : Lℂ^n) (hsa : is_sa T) : Lℂ^n :=
  @basis.constr (fin n) ℂ (ℂ^n) (ℂ^n) _ _ _ _ _ (e_vecs T hsa) ℂ _ _ _ (scaled_e_vecs T hsa)

def is_positive (T : Lℂ^n) :=
  (∀ x : ℂ^n, (⟪T x, x⟫_ℂ.re ≥ 0) ∧ (⟪T x, x⟫_ℂ.im = 0))

lemma lem_gram_self_adjoint :
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

theorem thm_7_35_a_b :
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

section sec_7_35_b_c

variable (i : fin n)

variable (hnn : ((e_vals T hsa) i) ≥ 0)

lemma lem_bc_0 :
  (sqrt T hsa) ((e_vecs T hsa) i) = real.sqrt ((e_vals T hsa) i) • ((e_vecs T hsa) i) :=
begin
  rw sqrt,
  rw basis.constr_basis,
  rw scaled_e_vecs,
end

lemma lem_bc_1 :
  ((sqrt T hsa) * (sqrt T hsa)) = T :=
begin
  apply basis.ext (e_vecs T hsa),
  intro i,
  let μi := (e_vals T hsa) i,
  let vi := (e_vecs T hsa) i,
  have h : T vi = μi • vi := by apply inner_product_space.is_self_adjoint.apply_eigenvector_basis,
  rw h,
  simp,
  rw lem_bc_0,
  sorry,
end

lemma lem_bc_2 :
  is_sa (sqrt T hsa) :=
begin
  rw self_adjoint_iff,
  rw linear_map.eq_adjoint_iff_basis (e_vecs T hsa) (e_vecs T hsa),
  intros i₁ i₂,
  rw lem_bc_0,
  rw lem_bc_0,
  sorry,
end

lemma lem_bc_3 :
  is_positive (sqrt T hsa) :=
begin
  rw is_positive,
  sorry,
end

theorem thm_7_35_b_c (hsa : is_sa T) :
  ∃ (R : Lℂ^n), ((R * R) = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  use (sqrt T hsa),
  split,
  apply lem_bc_1,
  split,
  apply lem_bc_2,
  apply lem_bc_3,
end

end sec_7_35_b_c

lemma lem_sqrt_gram :
  ∃ (R : Lℂ^n), (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  apply thm_7_35_b_c,
  exact lem_gram_self_adjoint T,
end