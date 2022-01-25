import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp

variable {n : ℕ}

open_locale big_operators complex_conjugate matrix

lemma self_adjoint_iff (T : module.End ℂ (euclidean_space ℂ (fin n))) :
  inner_product_space.is_self_adjoint T ↔ T = T.adjoint :=
begin
   rw linear_map.eq_adjoint_iff,
   rw inner_product_space.is_self_adjoint,
end

lemma lem_7_10 (T : module.End ℂ (euclidean_space ℂ (fin n))) :
  (linear_map.to_matrix' T.adjoint) = (linear_map.to_matrix' T)ᴴ :=
begin
  sorry,
end

lemma lem_7_13 (T : module.End ℂ (euclidean_space ℂ (fin n)))
  (hT : inner_product_space.is_self_adjoint T):
  ∀ (μ : ℂ) (h : T.has_eigenvalue μ), conj μ = μ :=
begin
  intro μ,
  intro h,
  rw inner_product_space.is_self_adjoint.conj_eigenvalue_eq_self
    hT h,
end

lemma lem_7_14 (T : module.End ℂ (euclidean_space ℂ (fin n)))
  (h : ∀ v : (euclidean_space ℂ (fin n)), ⟪T v, v⟫_ℂ = 0) : T = 0 :=
begin
  sorry,
end

lemma lem_7_15_eq (T : module.End ℂ (euclidean_space ℂ (fin n)))
  (v : (euclidean_space ℂ (fin n))) :
  ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
begin
  rw inner_conj_sym,
  rw ← linear_map.adjoint_inner_left,
  rw ← inner_sub_left,
  simp,
end

lemma lem_7_15 (T : module.End ℂ (euclidean_space ℂ (fin n))) :
  inner_product_space.is_self_adjoint T ↔
  ∀ v : (euclidean_space ℂ (fin n)), conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
begin
  split,
  {
    intro h,
    intro v,
    have fact₁ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
    begin
      rw lem_7_15_eq,
    end,
    have fact₂ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = 0 :=
    begin
      rw fact₁,
      rw self_adjoint_iff T at h,
      rw ← h,
      simp,
    end,
    rw sub_eq_zero at fact₂,
    symmetry,
    exact fact₂,
  },
  {
    intro hv,
    rw self_adjoint_iff,
    rw ← sub_eq_zero,
    apply lem_7_14,
    intro v,
    specialize hv v,
    have fact₃ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
    begin
      rw lem_7_15_eq,
    end,
    rw ← fact₃,
    rw sub_eq_zero,
    symmetry,
    exact hv,
  },
end
