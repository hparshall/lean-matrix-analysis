/-
The goal of this file is to prove that every positive, self-adjoint linear operator
on ℂ^n has a positive, self-adjoint square root.
-/

-- Checked over by:
-- Dan

/-
uses lem_7_15
-/
import .self_adjoint
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

lemma hn : finite_dimensional.finrank ℂ (ℂ^n) = n := finrank_euclidean_space_fin

local notation `ev` := hsa.eigenvalues hn
local notation `ew` := hsa.eigenvector_basis hn

local notation `sqrt_ew` := λ (i : (fin n)), (real.sqrt(((ev) i)) : ℂ) • ((ew) i)

noncomputable def sqrt : Lℂ^n :=
  @basis.constr (fin n) ℂ (ℂ^n) (ℂ^n) _ _ _ _ _ (ew) ℂ _ _ _ (sqrt_ew)

local notation `R` := (sqrt T) hsa


/-
T is positive, and so its eigenvalues are nonnegative.
-/

theorem eig_nonneg_of_pos (hpos : is_positive T):
  (∀ i : (fin n), 0 ≤ ((ev) i)) :=
  begin
    intro i,
    calc 0 ≤ ⟪ T ((hsa.eigenvector_basis hn) i), ((hsa.eigenvector_basis hn) i) ⟫_ℂ.re : (hpos (hsa.eigenvector_basis hn i)).1
      ... = ⟪ ↑((ev) i) • ((hsa.eigenvector_basis hn) i), ((hsa.eigenvector_basis hn) i) ⟫_ℂ.re : by {rw inner_product_space.is_self_adjoint.apply_eigenvector_basis hsa hn i}
      ... = ((ev) i • ⟪ ((hsa.eigenvector_basis hn) i), ((hsa.eigenvector_basis hn) i) ⟫_ℂ).re : by {rw @inner_smul_real_left ℂ _ _ _ ((hsa.eigenvector_basis hn) i) ((hsa.eigenvector_basis hn) i) ( ((ev) i))}
      ... = (ev) i : by {rw inner_self_eq_norm_sq_to_K, rw (hsa.eigenvector_basis_orthonormal hn).1, simp only [one_pow, mul_one, complex.real_smul, complex.of_real_one, complex.of_real_re, eq_self_iff_true]},
  end


/-
By definition, √T has the same eigenvectors as T, with sqrt eigenvalues.
-/

lemma sqrt_apply (i : fin n):
  R ((ew) i) = (real.sqrt ((ev) i) : ℂ) • ((ew) i) :=
begin
  rw [sqrt, (ew).constr_basis],
end

/-
We have √T^2 = T.
-/

lemma sqrt_sq (hpos : is_positive T):
  ((sqrt T hsa) * (sqrt T hsa)) = T :=
  begin
    apply basis.ext ew,
    intro i,
    calc (R * R) (ew i) = R (R (ew i)) : by {rw linear_map.mul_apply}
    ...                 = R (↑(real.sqrt(ev i)) • (ew i)) : by {rw sqrt_apply}
    ...                 = real.sqrt(ev i) • R ((ew i)) : by {rw linear_map.map_smul, norm_cast}
    ...                 = (ev i) • (ew i) : by {rw sqrt_apply, norm_cast, rw smul_smul, rw real.mul_self_sqrt, exact eig_nonneg_of_pos T hsa hpos i}
    ...                 = T (ew i) : by {rw inner_product_space.is_self_adjoint.apply_eigenvector_basis, norm_cast}
  end

/-
√T is self-adjoint.
-/

lemma sqrt_is_sa (hpos : is_positive T) :
  is_sa R :=
  begin
    rw [is_self_adjoint_iff_eq_adjoint, linear_map.eq_adjoint_iff_basis (ew) (ew)],
    intros i j,
    by_cases h : (i = j),
    iterate {rw ← h},
    calc ⟪ R ((ew) i), (ew) i ⟫_ℂ = real.sqrt((ev) i) • ⟪ (ew) i, (ew) i ⟫_ℂ : by {rw sqrt_apply, rw [inner_smul_left, complex.conj_of_real, complex.real_smul]}
      ...                         = ⟪ (ew) i, R ((ew) i) ⟫_ℂ : by {rw sqrt_apply, rw [inner_smul_right, complex.real_smul]},

    calc ⟪ R ((ew) i), (ew) j ⟫_ℂ = real.sqrt((ev) i) • ⟪ (ew) i, (ew) j ⟫_ℂ : by {rw sqrt_apply, rw [inner_smul_left, complex.conj_of_real, complex.real_smul]}
      ...                         = ⟪ (ew) i, R ((ew) j) ⟫_ℂ : by {rw sqrt_apply, rw [inner_smul_right, complex.real_smul, (hsa.eigenvector_basis_orthonormal hn).2 h, mul_zero, mul_zero]},
  end


/-
√T scales basis coordinates by sqrt eigenvalues.
-/

lemma sqrt_repr (x : ℂ^n) (i : fin n) (hpos : is_positive T):
  (ew).repr (R x) i = (real.sqrt((ev) i)) • ((ew).repr x i) :=
begin
  calc (ew).repr(R x) i = ⟪ (ew) i, R x ⟫_ℂ : onb_coords_eq_inner _ _ _ (inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal hsa hn)
    ...                 = ⟪ R ((ew) i) , x ⟫_ℂ : (sqrt_is_sa T hsa hpos ((ew) i) x).symm
    ...                 = (real.sqrt((ev) i)) • ⟪ (ew) i , x ⟫_ℂ : by {rw [sqrt_apply, inner_smul_left, is_R_or_C.conj_of_real, complex.real_smul]}
    ...                 = (real.sqrt((ev) i)) • ((ew).repr x i) : by {rw ← onb_coords_eq_inner (ew) _ _ (inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal hsa hn)},
end

/-
√T is positive, real part.
-/

lemma sqrt_is_positive' (hpos : is_positive T) (x : ℂ^n) :
  ⟪ (sqrt T hsa) x, x ⟫_ℂ.re ≥ 0 :=
  begin
    rw [← basis.sum_repr (ew) (R x), sum_inner, ← complex.coe_re_add_group_hom, add_monoid_hom.map_sum complex.re_add_group_hom],
    apply finset.sum_nonneg,
    intros i hi,
    calc 0 ≤ real.sqrt ((ev) i) * complex.norm_sq(((ew).repr x) i ) : mul_nonneg (real.sqrt_nonneg ((ev) i)) (complex.norm_sq_nonneg _)
    ...    = (conj (real.sqrt ((ev) i) • ((ew).repr x) i) * ((ew).repr x) i ).re : by {rw [is_R_or_C.conj_smul, smul_mul_assoc, complex.smul_re, ← complex.norm_sq_eq_conj_mul_self], norm_cast}
    ...    = complex.re_add_group_hom (⟪ ((ew).repr (R x) i) • ((ew) i), x ⟫_ℂ) : by {rw [@sqrt_repr _ _ hsa x i _, inner_smul_left, onb_coords_eq_inner (ew) x i (inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal hsa hn), complex.coe_re_add_group_hom], exact hpos},
  end

/-
√T is positive.
-/

lemma sqrt_is_positive (hpos : is_positive T) :
  is_positive (sqrt T hsa) :=
begin
  intro x,
  exact ⟨sqrt_is_positive' T hsa hpos x, complex.eq_conj_iff_im.1 ((is_self_adjoint_iff_real_inner_map R).1 (sqrt_is_sa T hsa hpos) x)⟩,
end


/-
A positive, self-adjoint linear operator T : ℂ^n → ℂ^n has a positive, self-adjoint square root.
-/
theorem sqrt_exists (hsa : is_sa T) (hpos : is_positive T):
  ∃ (R' : Lℂ^n), ((R' * R') = T) ∧ (is_sa R') ∧ (is_positive R') :=
    Exists.intro (sqrt T hsa) (id ⟨sqrt_sq T hsa hpos, ⟨sqrt_is_sa T hsa hpos, sqrt_is_positive T hsa hpos⟩⟩)