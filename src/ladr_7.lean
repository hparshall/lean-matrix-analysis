import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import .lemmas.ladr_7_lem

variable {n : ℕ}

open_locale big_operators complex_conjugate matrix

lemma self_adjoint_iff (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T ↔ T = T.adjoint :=
begin
   rw linear_map.eq_adjoint_iff,
   rw inner_product_space.is_self_adjoint,
end

lemma lem_7_10 (T : Lℂ^n) :
  (linear_map.to_matrix' T.adjoint) = (linear_map.to_matrix' T)ᴴ :=
begin
  sorry,
end

lemma lem_7_13 (T : Lℂ^n)
  (hT : inner_product_space.is_self_adjoint T):
  ∀ (μ : ℂ) (h : T.has_eigenvalue μ), conj μ = μ :=
begin
  intro μ,
  intro h,
  rw inner_product_space.is_self_adjoint.conj_eigenvalue_eq_self
    hT h,
end

lemma lem_7_14 (T : Lℂ^n)
  (h : ∀ v : ℂ^n, ⟪T v, v⟫_ℂ = 0) : T = 0 :=
begin
  have calculation : ∀ u w : ℂ^n, 
    4 • ⟪T u, w ⟫_ℂ = ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + complex.I • ⟪T (u + complex.I • w) , u + complex.I • w⟫_ℂ - complex.I • ⟪T (u - complex.I • w), u - complex.I • w ⟫_ℂ :=
    begin
      intros u w,
      ring_nf,
      sorry,
    end,
  have : ∀ u w : ℂ^n, 4 • ⟪T u, w ⟫_ℂ = 0 :=
    begin
      intros u w,
      calc 4 • ⟪T u, w ⟫_ℂ = ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + complex.I • ⟪T (u + complex.I • w) , u + complex.I • w⟫_ℂ - complex.I • ⟪T (u - complex.I • w), u - complex.I • w ⟫_ℂ : calculation u w
      ...                  = - ⟪T (u - w) , u - w⟫_ℂ + complex.I • ⟪T (u + complex.I • w) , u + complex.I • w⟫_ℂ - complex.I • ⟪T (u - complex.I • w), u - complex.I • w ⟫_ℂ : by {rw h (u + w), ring}
      ...                  = complex.I • ⟪T (u + complex.I • w) , u + complex.I • w⟫_ℂ - complex.I • ⟪T (u - complex.I • w), u - complex.I • w ⟫_ℂ : by {rw h (u - w), ring}
      ...                  = - (complex.I • ⟪T (u - complex.I • w), u - complex.I • w ⟫_ℂ) : by {rw h (u + complex.I • w), rw smul_zero, ring}
      ...                  = 0 : by {rw h (u - complex.I • w), rw smul_zero, ring},
    end,
  apply linear_map.ext,
  intro x,
  specialize this x,
  have : T x = 0,
  begin
    apply inner_with_all_eq_zero_eq_zero,
    intro u,
    
  end
end

lemma lem_7_15_eq (T : Lℂ^n)
  (v : ℂ^n) :
  ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
begin
  rw inner_conj_sym,
  rw ← linear_map.adjoint_inner_left,
  rw ← inner_sub_left,
  simp,
end

lemma lem_7_15 (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T ↔
  ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
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

def is_normal (T : Lℂ^n) :=
  T*(T.adjoint) = (T.adjoint)*T

lemma lem_7_20 (T : Lℂ^n) :
  (is_normal T) ↔
  ∀ v : ℂ^n,
    ∥T v∥ = ∥(linear_map.adjoint T) v∥ :=
  begin
    sorry,
  end

lemma lem_7_21 (T : Lℂ^n)
  (μ : ℂ) (v : ℂ^n)
  (hT : is_normal T) (hv : T.has_eigenvector μ v) :
  module.End.has_eigenvector (T.adjoint) (conj μ) v :=
begin
  sorry,
end

lemma lem_7_22 (T : Lℂ^n)
  (μ₁ μ₂ : ℂ) (v₁ v₂ : ℂ^n)
  (hT : is_normal T) (hμ₁ : T.has_eigenvector μ₁ v₁) (hμ₂ : T.has_eigenvector μ₂ v₂)
  (hneq : μ₁ ≠ μ₂) : ⟪v₁,v₂⟫_ℂ = 0 :=
begin
  sorry,
end