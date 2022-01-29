import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem
import .ladr_7

open_locale big_operators complex_conjugate matrix

notation `is_sa` := inner_product_space.is_self_adjoint

variables {n : ℕ} (T : Lℂ^n) (hsa : is_sa T) (i : fin n)

lemma hn : finite_dimensional.finrank ℂ (ℂ^n) = n := by exact finrank_euclidean_space_fin

noncomputable def e_vals : (fin n → ℝ) :=
  inner_product_space.is_self_adjoint.eigenvalues hsa hn

noncomputable def e_vecs : (basis (fin n) ℂ (ℂ^n)) :=
  @inner_product_space.is_self_adjoint.eigenvector_basis ℂ _ _ (ℂ^n) _ T hsa _ n hn

noncomputable def scaled_e_vecs : (fin n) → ℂ^n :=
  λ (i : (fin n)), (real.sqrt(((e_vals T hsa) i)) : ℂ) • ((e_vecs T hsa) i)

noncomputable def sqrt : Lℂ^n :=
  @basis.constr (fin n) ℂ (ℂ^n) (ℂ^n) _ _ _ _ _ (e_vecs T hsa) ℂ _ _ _ (scaled_e_vecs T hsa)

def is_positive :=
  (∀ x : ℂ^n, (⟪T x, x⟫_ℂ.re ≥ 0) ∧ (⟪T x, x⟫_ℂ.im = 0))

variable (hpos : is_positive T)

theorem thm_7_35_a_b (hsa : is_sa T):
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

lemma lem_bc_2 (hpos : is_positive T) :
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

lemma evecs_on (i j : fin n) : ⟪ (e_vecs T hsa) i, (e_vecs T hsa) j ⟫_ℂ = ite (i = j) 1 0 :=
begin
  have hon : orthonormal ℂ (e_vecs T hsa) := by apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  rw orthonormal_iff_ite at hon,
  specialize hon i j,
  exact hon,
end

lemma inner_evec_coords (x : ℂ^n) (i : fin n) :
  ⟪ ((e_vecs T hsa) i), x ⟫_ℂ = (e_vecs T hsa).repr x i :=
begin
  have hon : orthonormal ℂ (e_vecs T hsa) := by apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  rw orthonormal_iff_ite at hon,
  conv
  begin
    to_lhs,
    rw ← basis.sum_repr (e_vecs T hsa) x,
    rw inner_sum,
    congr,
    skip,
    funext,
    rw inner_smul_right,
    dedup,
    rw evecs_on,
    simp,
  end,
  rw finset.sum_ite,
  simp,
  rw finset.filter_eq,
  simp,
end

lemma sqrt_repr (x : ℂ^n) (i : fin n) (hpos : is_positive T):
  (e_vecs T hsa).repr ((sqrt T hsa) x) i = (real.sqrt(e_vals T hsa i)) • ((e_vecs T hsa).repr x i) :=
begin
  rw ← inner_evec_coords,
  rw ← inner_evec_coords,
  have hsqrt : is_sa (sqrt T hsa) :=
  begin
    apply lem_bc_2,
    exact hpos,
  end,
  rw self_adjoint_iff at hsqrt,
  rw linear_map.eq_adjoint_iff at hsqrt,
  specialize hsqrt ((e_vecs T hsa) i) x,
  rw ← hsqrt,
  rw lem_bc_0,
  rw inner_smul_left,
  simp,
end

lemma lem_bc_3a (hpos : is_positive T) (x : ℂ^n) :
  ⟪ (sqrt T hsa) x, x ⟫_ℂ.re ≥ 0 :=
begin
  rw ← basis.sum_repr (e_vecs T hsa) ((sqrt T hsa) x),
  rw sum_inner,
  conv
  begin
    to_lhs,
    congr,
    congr,
    skip,
    funext,
    rw sqrt_repr T hsa x i hpos,
    rw inner_smul_left,
    rw inner_evec_coords,
    rw is_R_or_C.conj_smul,
    rw smul_mul_assoc,
    rw ← complex.norm_sq_eq_conj_mul_self,
  end,
  norm_cast,
  apply finset.sum_nonneg',
  intro i,
  have hnn : (∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :=
  begin
    apply thm_7_35_a_b,
    exact hpos,
  end,
  specialize hnn i,
  by_cases hz : (e_vals T hsa) i = 0,
  rw hz,
  simp,
  rw ne.le_iff_lt at hnn,
  rw ← real.sqrt_pos at hnn,
  rw ← div_le_iff',
  simp,
  apply complex.norm_sq_nonneg,
  exact hnn,
  symmetry,
  norm_cast,
  exact hz,
end

lemma lem_bc_3 (hpos : is_positive T) :
  is_positive (sqrt T hsa) :=
begin
  let R := (sqrt T hsa),
  have hsaR : (is_sa R) := by exact lem_bc_2 T hsa hpos,
  rw is_positive,
  intro x,
  rw lem_7_15 at hsaR,
  split,
  apply lem_bc_3a,
  exact hpos,
  specialize hsaR x,
  rw ← complex.eq_conj_iff_im,
  exact hsaR,
end

theorem thm_7_35_b_c (hpos : is_positive T) (hsa : is_sa T) (hnn : ∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)):
  ∃ (R : Lℂ^n), ((R * R) = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  use (sqrt T hsa),
  split,
  apply lem_bc_1,
  exact hnn,
  split,
  apply lem_bc_2,
  exact hpos,
  apply lem_bc_3,
  exact hpos,
end