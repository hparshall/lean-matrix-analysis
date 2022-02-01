/-
The goal of this file is to prove the following.  If S ⊆ ℂ^n is a subspace and L : S → V is
an isometry, then there exists an isometry M : ℂ^n → ℂ^n such that M(s) = L(s) for every s ∈ S.

In other words, every isometry on a subspace of ℂ^n extends to an isometry of ℂ^n.
-/

import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (S : submodule ℂ (ℂ^n))

local attribute [instance] fact_one_le_two_real

/-
S is also a finite dimensional inner product space.
-/

noncomputable lemma hS_module : module ℂ S := by apply submodule.module

noncomputable lemma hS_ips : inner_product_space ℂ S := by apply submodule.inner_product_space

lemma hS_fd : finite_dimensional ℂ S := by apply finite_dimensional.finite_dimensional_submodule

/-
S has an orthonormal basis.
-/

noncomputable def onbasis := orthonormal_basis ℂ S

lemma hb_on : orthonormal ℂ (onbasis S) := by apply orthonormal_basis_orthonormal

/-
Let L : S → ℂ^n be an isometry.
-/

variable (L : S →ₗᵢ[ℂ] ℂ^n)

lemma hLS_on : orthonormal ℂ (L ∘ onbasis S) :=
  by apply orthonormal.comp_linear_isometry (hb_on S)

-- need to coerce basis elements in S to vectors in ℂ^n
-- noncomputable def extend_S_onb (hv: orthonormal ℂ (coe_fn (onbasis S) : (orthonormal_basis_index ℂ S) → ℂ^n)) :=
--   classical.some (exists_subset_is_orthonormal_basis hv)