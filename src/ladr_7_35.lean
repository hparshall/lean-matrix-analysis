/-
The goal of this file is to prove that every positive, self-adjoint linear operator
on ℂ^n has a positive, self-adjoint square root.
-/


/-
uses lem_7_15
-/
import .ladr_7
import .orthonormal_basis

open_locale big_operators complex_conjugate matrix

notation `is_sa` := inner_product_space.is_self_adjoint

/-
Throughout, T is a positive, self-adjoint linear operator on ℂ^n.
-/

variables {n : ℕ} (T : Lℂ^n) (hsa : is_sa T)

def is_positive :=
  (∀ x : ℂ^n, (⟪T x, x⟫_ℂ.re ≥ 0) ∧ (⟪T x, x⟫_ℂ.im = 0))

variable (hpos : is_positive T)

/-
The spectral theorem allows us to define √T
-/

lemma hn : finite_dimensional.finrank ℂ (ℂ^n) = n := by exact finrank_euclidean_space_fin

noncomputable def e_vals : (fin n → ℝ) := hsa.eigenvalues hn

noncomputable def e_vecs : (basis (fin n) ℂ (ℂ^n)) := hsa.eigenvector_basis hn

noncomputable def scaled_e_vecs : (fin n) → ℂ^n :=
  λ (i : (fin n)), (real.sqrt(((e_vals T hsa) i)) : ℂ) • ((e_vecs T hsa) i)

noncomputable def sqrt : Lℂ^n :=
  @basis.constr (fin n) ℂ (ℂ^n) (ℂ^n) _ _ _ _ _ (e_vecs T hsa) ℂ _ _ _ (scaled_e_vecs T hsa)

/-
T is positive, and so its eigenvalues are nonnegative.
-/

theorem thm_7_35_a_b (hpos : is_positive T):
  (∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :=
begin
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
      simp only [ne.def, not_false_iff, one_ne_zero],
    end,
    rw hite at hon,
    exact hon,
  end,
  have hip : ⟪T v, v⟫_ℂ = (conj μ) :=
  begin
    rw hμ,
    rw inner_smul_left,
    rw hn,
    simp only [complex.of_real_inj, is_R_or_C.conj_to_real, is_R_or_C.conj_of_real, mul_one, eq_self_iff_true],
  end,
  rw is_positive at hpos,
  specialize hpos v,
  cases hpos with hre him,
  rw hip at hre,
  norm_cast at hre,
  rw is_R_or_C.conj_to_real at hre,
  exact hre,
end

/-
By definition, √T has the same eigenvectors as T, with sqrt eigenvalues.
-/

lemma lem_bc_0 (i : fin n):
  (sqrt T hsa) ((e_vecs T hsa) i) = (real.sqrt ((e_vals T hsa) i) : ℂ) • ((e_vecs T hsa) i) :=
begin
  rw sqrt,
  rw basis.constr_basis,
  rw scaled_e_vecs,
end

/-
We have √T^2 = T.
-/

lemma lem_bc_1 (hpos : is_positive T):
  ((sqrt T hsa) * (sqrt T hsa)) = T :=
begin
  apply basis.ext (e_vecs T hsa),
  intro i,
  let μi := (e_vals T hsa) i,
  let vi := (e_vecs T hsa) i,
  have h : T vi = μi • vi := by apply inner_product_space.is_self_adjoint.apply_eigenvector_basis,
  rw h,
  rw linear_map.mul_apply,
  rw lem_bc_0,
  rw linear_map.map_smul,
  rw lem_bc_0,
  rw smul_smul,
  norm_cast,
  rw real.mul_self_sqrt,
  have hab : (∀ i : (fin n), 0 ≤ ((e_vals T hsa) i)) :=
  begin
    apply thm_7_35_a_b,
    exact hpos
  end,
  specialize hab i,
  exact hab,
end

/-
√T is self-adjoint.
-/

lemma lem_bc_2 (hpos : is_positive T) :
  is_sa (sqrt T hsa) :=
begin
  rw self_adjoint_iff_eq_adjoint,
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
  simp only [mul_boole],
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

/-
√T scales basis coordinates by sqrt eigenvalues.
-/

lemma sqrt_repr (x : ℂ^n) (i : fin n) (hpos : is_positive T):
  (e_vecs T hsa).repr ((sqrt T hsa) x) i = (real.sqrt(e_vals T hsa i)) • ((e_vecs T hsa).repr x i) :=
begin
  rw onb_coords_eq_inner,
  rw onb_coords_eq_inner,
  have hsqrt : is_sa (sqrt T hsa) :=
  begin
    apply lem_bc_2,
    exact hpos,
  end,
  rw self_adjoint_iff_eq_adjoint at hsqrt,
  rw linear_map.eq_adjoint_iff at hsqrt,
  specialize hsqrt ((e_vecs T hsa) i) x,
  rw ← hsqrt,
  rw lem_bc_0,
  rw inner_smul_left,
  simp only [is_R_or_C.inner_apply,
    is_R_or_C.conj_of_real,
    complex.real_smul,
    mul_eq_mul_left_iff,
    pi_Lp.inner_apply,
    true_or,
    eq_self_iff_true,
    complex.of_real_eq_zero,
    finset.sum_congr],
  apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
end

/-
√T is positive, real part.
-/

lemma lem_bc_3a (hpos : is_positive T) (x : ℂ^n) :
  ⟪ (sqrt T hsa) x, x ⟫_ℂ.re ≥ 0 :=
begin
  rw ← basis.sum_repr (e_vecs T hsa) ((sqrt T hsa) x),
  rw sum_inner,
  have hon : orthonormal ℂ (e_vecs T hsa) := by apply inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal,
  conv
  begin
    to_lhs,
    congr,
    congr,
    skip,
    funext,
    rw sqrt_repr T hsa x i hpos,
    rw inner_smul_left,
    rw ← onb_coords_eq_inner (e_vecs T hsa) x i hon,
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
  simp only [le_refl, real.sqrt_zero, zero_mul],
  rw ne.le_iff_lt at hnn,
  rw ← real.sqrt_pos at hnn,
  rw ← div_le_iff',
  simp only [zero_div],
  apply complex.norm_sq_nonneg,
  exact hnn,
  symmetry,
  norm_cast,
  exact hz,
end

/-
√T is positive.
-/

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


/-
A positive, self-adjoint linear operator T : ℂ^n → ℂ^n has a positive, self-adjoint square root.
-/
theorem thm_7_35_b_c (hsa : is_sa T) (hpos : is_positive T):
  ∃ (R : Lℂ^n), ((R * R) = T) ∧ (is_sa R) ∧ (is_positive R) :=
begin
  use (sqrt T hsa),
  split,
  apply lem_bc_1,
  exact hpos,
  split,
  apply lem_bc_2,
  exact hpos,
  apply lem_bc_3,
  exact hpos,
end