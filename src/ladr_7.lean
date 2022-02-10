import .lemmas.ladr_7_lem

variable {n : ℕ}

localized "postfix `†`:1000 := linear_map.adjoint" in src

open_locale big_operators complex_conjugate matrix

lemma self_adjoint_iff_eq_adjoint (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T ↔ T = T.adjoint :=
begin
   rw linear_map.eq_adjoint_iff,
   rw inner_product_space.is_self_adjoint,
end

/-
independent
-/
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

/-
uses inner_map_add_add, inner_map_sub_sub
-/
lemma lem_7_14_a (T : Lℂ^n) (u w : ℂ^n): ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ = 4 * ⟪ T w, u ⟫_ℂ :=
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

/-
uses lem_7_14_a
-/
lemma lem_7_14_b (T : Lℂ^n) : ∀ u w : ℂ^n,
    4 * ⟪T w, u ⟫_ℂ = ⟪T (u + w) , u + w⟫_ℂ - ⟪T (u - w) , u - w⟫_ℂ + I * ⟪T (u + I • w) , u + I • w⟫_ℂ - I * ⟪T (u - I • w), u - I • w ⟫_ℂ :=
begin
  intros u w,
  rw lem_7_14_a,
end

/-
uses lem_7_14_b
-/
lemma lem_7_14 (T : Lℂ^n)
  (h : ∀ v : ℂ^n, ⟪T v, v⟫_ℂ = 0) : T = 0 :=
begin
  have : ∀ u w : ℂ^n, 4 * ⟪T u, w ⟫_ℂ = 0 :=
    begin
      intros u w,
      rw lem_7_14_b,
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

lemma lem_7_15_eq (T : Lℂ^n)
  (v : ℂ^n) :
  ⟪T v, v⟫_ℂ - conj ⟪T v, v⟫_ℂ = ⟪ (T - T.adjoint) v, v⟫_ℂ :=
begin
  rw inner_conj_sym,
  rw ← linear_map.adjoint_inner_left,
  rw ← inner_sub_left,
  simp,
end

/-
uses lem_7_15_eq and lem_7_14
-/
lemma lem_7_15 (T : Lℂ^n) :
  inner_product_space.is_self_adjoint T
    ↔ ∀ v : ℂ^n, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
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
      rw self_adjoint_iff_eq_adjoint T at h,
      rw ← h,
      simp,
    end,
    rw sub_eq_zero at fact₂,
    symmetry,
    exact fact₂,
  },
  {
    intro hv,
    rw self_adjoint_iff_eq_adjoint,
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