import analysis.inner_product_space.adjoint
import .orthonormal_basis

variable {n : ℕ}

notation `ℂ^` n := euclidean_space ℂ (fin n)

notation `Lℂ^` n := module.End ℂ ℂ^n

notation `I` := complex.I

open_locale complex_conjugate

lemma inner_with_all_eq_zero_eq_zero (v : ℂ^ n) : (∀ u : ℂ^n, ⟪u, v⟫_ℂ = 0) → v = 0 :=
begin
  intro h,
  specialize h v,
  rw inner_self_eq_zero at h,
  exact h,
end

lemma inner_map_add_add (T : Lℂ^n) (u w : ℂ^n) : ⟪ T (u + w), u + w ⟫_ℂ = ⟪T u, u⟫_ℂ + ⟪T w, u⟫_ℂ + ⟪T u, w⟫_ℂ + ⟪T w, w⟫_ℂ :=
begin
  rw map_add,
  rw [inner_add_left, inner_add_right, inner_add_right],
  ring,
end

lemma inner_map_sub_sub (T : Lℂ^n) (u w : ℂ^n) : ⟪ T (u - w), u - w ⟫_ℂ = ⟪T u, u⟫_ℂ - ⟪T w, u⟫_ℂ - ⟪T u, w⟫_ℂ + ⟪T w, w⟫_ℂ :=
begin
  rw map_sub,
  rw [inner_sub_left, inner_sub_right, inner_sub_right],
  ring,
end

lemma identity_one (T : Lℂ^n) (u w : ℂ^n): ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ = 4 * ⟪ T w, u ⟫_ℂ :=
begin
  calc ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ
      = ⟪T u, u⟫_ℂ + ⟪T w, u⟫_ℂ + ⟪T u, w⟫_ℂ + ⟪T w, w⟫_ℂ - ⟪T u, u⟫_ℂ + ⟪T w, u⟫_ℂ + ⟪T u, w⟫_ℂ - ⟪T w, w⟫_ℂ + I * ⟪T u, u⟫_ℂ - ⟪T u, w⟫_ℂ + ⟪T w, u⟫_ℂ - I * ⟪T w, w⟫_ℂ - I * ⟪T u, u⟫_ℂ + ⟪T w, u⟫_ℂ - ⟪T u, w⟫_ℂ + I * ⟪T w, w⟫_ℂ : by
      {
        rw [inner_map_add_add, inner_map_add_add],
        rw [inner_map_sub_sub, inner_map_sub_sub],
        ring_nf,
        rw linear_map.map_smul,
        rw [inner_smul_left, inner_smul_right],
        rw [complex.conj_I, add_mul _ _ I, mul_comm _ I, ← mul_assoc I _ _, mul_comm I 2, ← mul_assoc (2 * I) _ _],
        ring_nf,
        rw complex.I_sq,
        ring_nf,
      }
  ...  = 4 * ⟪ T w , u⟫_ℂ : by
  {
    ring_nf,
  },
end

lemma identity_two (T : Lℂ^n) : ∀ u w : ℂ^n,
    4 * ⟪T w, u ⟫_ℂ = ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ :=
begin
  intros u w,
  rw identity_one,
end

lemma inner_eq_zero_iff_zero (T : Lℂ^n)
  (h : ∀ v : ℂ^n, ⟪T v, v⟫_ℂ = 0) : T = 0 :=
begin
  have : ∀ u w : ℂ^n, 4 * ⟪T u, w ⟫_ℂ = 0 :=
    begin
      intros u w,
      rw identity_two,
      iterate {rw h},
      ring,
    end,
  apply linear_map.ext,
  intro x,
  specialize this x,
  have : T x = 0,
  begin
    apply inner_with_all_eq_zero_eq_zero,
    intro u,
    calc ⟪u, (T x)⟫_ℂ = conj ⟪(T x), u⟫_ℂ : by {rw ← inner_conj_sym}
    ...                = (1 / 4) * (4 * conj ⟪(T x), u⟫_ℂ ) : by {ring}
    ...                = (1 / 4) * conj (4 * ⟪(T x), u⟫_ℂ ) : by {simp}
    ...                = (1 / 4) * conj 0 : by {rw this u}
    ...                = 0 : by {simp},
  end,
  rw this,
  simp,
end

lemma inner_sub_eq_inner_sub_adjoint (T : Lℂ^n)
  (v : ℂ^n) :
  ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
begin
  rw inner_conj_sym,
  rw ← linear_map.adjoint_inner_left,
  rw ← inner_sub_left,
  simp,
end

lemma self_adjoint_iff (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T ↔ T = T.adjoint :=
begin
   rw linear_map.eq_adjoint_iff,
   rw inner_product_space.is_self_adjoint,
end

lemma self_adjoint_iff_inner_real (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T
    ↔ ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
begin
  split,
  {
    intro h,
    intro v,
    have fact₁ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
    begin
      rw inner_sub_eq_inner_sub_adjoint,
    end,
    have fact₂ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = 0 :=
    begin
      rw inner_product_space.is_self_adjoint.conj_inner_sym,
      simp only [is_R_or_C.inner_apply, pi_Lp.inner_apply, eq_self_iff_true, finset.sum_congr, sub_self],
      exact h,
    end,
    rw sub_eq_zero at fact₂,
    symmetry,
    exact fact₂,
  },
  {
    intro hv,
    rw self_adjoint_iff,
    rw ← sub_eq_zero,
    apply inner_eq_zero_iff_zero,
    intro v,
    specialize hv v,
    have fact₃ : ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
    begin
      rw inner_sub_eq_inner_sub_adjoint,
    end,
    rw ← fact₃,
    rw sub_eq_zero,
    symmetry,
    exact hv,
  },
end