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
  λ (i : (fin n)), (real.sqrt(((e_vals T hsa) i)) : ℂ) • ((e_vecs T hsa) i)

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
  is_positive T → (∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :=
begin
  intro hpos,
  intro i,
  let μ := (e_vals T hsa) i,
  let v := (e_vecs T hsa) i,
  have hv : T.has_eigenvector μ v := by apply inner_product_space.is_self_adjoint.has_eigenvector_eigenvector_basis,
  have hμ : T v = (μ : ℂ) • v := by apply module.End.has_eigenvector.apply_eq_smul hv,
  have hon : orthonormal ℂ (e_vecs T hsa) := by apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  have hn : ⟪v, v⟫_ℂ = 1 :=
  begin
    rw orthonormal_iff_ite at hon,
    specialize hon i i,
    have hite : ite (i = i) (1 : ℂ) (0 : ℂ) = (1 : ℂ) :=
    begin
      rw ne.ite_eq_left_iff,
      simp,
    end,
    rw hite at hon,
    exact hon,
  end,
  have hip : ⟪T v, v⟫_ℂ = (conj μ) :=
  begin
    rw hμ,
    rw inner_smul_left,
    rw hn,
    simp,
  end,
  rw is_positive at hpos,
  specialize hpos v,
  cases hpos with hre him,
  rw hip at hre,
  norm_cast at hre,
  simp at hre,
  exact hre,
end

section sec_7_35_b_c

variable (i : fin n)

lemma lem_bc_0 :
  (sqrt T hsa) ((e_vecs T hsa) i) = (real.sqrt ((e_vals T hsa) i) : ℂ) • ((e_vecs T hsa) i) :=
begin
  rw sqrt,
  rw basis.constr_basis,
  rw scaled_e_vecs,
end

lemma sqrt_sqrt (hnn : 0 ≤ ((e_vals T hsa) i)):
  (real.sqrt ((e_vals T hsa) i) : ℂ) * (real.sqrt ((e_vals T hsa) i) : ℂ) = (e_vals T hsa) i :=
begin
  norm_cast,
  rw real.mul_self_sqrt,
  exact hnn,
end

lemma lem_bc_1 (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)):
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
  rw linear_map.map_smul,
  rw lem_bc_0,
  rw smul_smul,
  rw sqrt_sqrt,
  norm_cast,
  specialize hnn i,
  exact hnn,
end

lemma lem_bc_2 (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :
  is_sa (sqrt T hsa) :=
begin
  rw self_adjoint_iff,
  rw linear_map.eq_adjoint_iff_basis (e_vecs T hsa) (e_vecs T hsa),
  intros i j,
  rw lem_bc_0,
  rw lem_bc_0,
  rw inner_smul_left,
  rw inner_smul_right,
  have hc : conj (real.sqrt (e_vals T hsa i) : ℂ) = (real.sqrt (e_vals T hsa i) : ℂ) :=
  begin
    rw complex.eq_conj_iff_real,
    use (real.sqrt (e_vals T hsa i)),
  end,
  rw hc,
  have hon : orthonormal ℂ (e_vecs T hsa) := by apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  rw orthonormal_iff_ite at hon,
  specialize hon i j,
  rw hon,
  by_cases hij : (i = j),
  rw hij,
  simp,
  have hi : ite (i = j) (real.sqrt (e_vals T hsa i) : ℂ) 0 = 0 :=
  begin
    rw ← ite_not,
    rw ite_eq_left_iff,
    tauto,
  end,
  have hj : ite (i = j) (real.sqrt (e_vals T hsa j) : ℂ) 0 = 0 :=
  begin
    rw ← ite_not,
    rw ite_eq_left_iff,
    tauto,
  end,
  rw hi,
  rw hj,
end

lemma lem_bc_3a (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) (x : ℂ^n) :
  ⟪ (sqrt T hsa) x, x ⟫_ℂ.re ≥ 0 :=
begin
  -- proof on paper:  expand x w.r.t. the o.n. basis of eigenvectors
  -- how to complete here?
  sorry,
end

lemma lem_bc_3 (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :
  is_positive (sqrt T hsa) :=
begin
  let R := (sqrt T hsa),
  have hsaR : (is_sa R) := by exact lem_bc_2 T hsa hnn,
  rw is_positive,
  intro x,
  rw lem_7_15 at hsaR,
  split,
  apply lem_bc_3a,
  exact hnn,
  specialize hsaR x,
  rw ← complex.eq_conj_iff_im,
  exact hsaR,
end

theorem thm_7_35_b_c (hsa : is_sa T) (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)):
  ∃ (R : Lℂ^n), ((R * R) = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  use (sqrt T hsa),
  split,
  apply lem_bc_1,
  exact hnn,
  split,
  apply lem_bc_2,
  exact hnn,
  apply lem_bc_3,
  exact hnn,
end

end sec_7_35_b_c

lemma lem_sqrt_gram :
  ∃ (R : Lℂ^n), (R^2 = T.adjoint * T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  have hg : is_sa (T.adjoint * T) := by exact lem_gram_self_adjoint T,
  apply thm_7_35_b_c,
  apply thm_7_35_a_b,
  rw is_positive,
  intro x,
  have h1 : ⟪ (T.adjoint * T) x, x ⟫_ℂ = ⟪ (linear_map.adjoint T) (T x), x ⟫_ℂ :=
  begin
    rw linear_map.mul_apply,
  end,
  rw h1,
  rw linear_map.adjoint_inner_left,
  rw ← is_R_or_C.re_to_complex,
  rw ← is_R_or_C.im_to_complex,
  rw inner_self_eq_norm_sq,
  norm_cast,
  split,
  exact sq_nonneg (∥ T x ∥),
  rw inner_self_nonneg_im,
  exact hg,
end