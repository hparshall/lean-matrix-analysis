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


/-
most of what follows seems low-priority
-/


-- lemma lem_7_16 (T : Lℂ^n) (hT : T = T†) (hInner : ∀ v : ℂ^n, ⟪ T v , v ⟫_ℂ = 0) : T = 0 :=
-- begin
--   exact lem_7_14 _ hInner,
-- end

-- def is_normal (T : Lℂ^n) :=
--   T*(T.adjoint) = (T.adjoint)*T


-- lemma lem_7_20_1_a (T : Lℂ^n) (hT : is_normal T) (v : ℂ^n) : ⟪ (T * T.adjoint) v, v ⟫_ℂ = ⟪ (T.adjoint * T) v, v ⟫_ℂ :=
-- begin
--     have fact₁: (T * (T.adjoint)) v - ((T.adjoint * T) v) = 0 :=
--     begin
--       rw is_normal at hT,
--       rw hT,
--       rw sub_self,
--     end,
--     have fact₂ : ⟪(T * (T† )) v - ((T† * T) v), v ⟫_ℂ = 0 :=
--     begin
--       rw fact₁,
--       rw inner_zero_left,
--     end,
--   rw inner_sub_left at fact₂,
--   rw eq_add_of_sub_eq fact₂,
--   ring,
-- end

-- lemma lem_7_20_1_b (T : Lℂ^n) (hT : is_normal T) (v : ℂ^n) : (∥ T v ∥^2 : ℂ ) = (∥ T† v ∥^2 : ℂ) :=
-- begin
--   calc (∥ T v ∥^2 : ℂ) = ⟪ T v , T v ⟫_ℂ : by {rw inner_self_eq_norm_sq_to_K}
--   ...            =  ⟪ (T†) (T v), v ⟫_ℂ : by {rw linear_map.adjoint_inner_left T}
--   ...            =  ⟪ ((T†) * T) v, v ⟫_ℂ : by {rw comp_eq_mul}
--   ...            =  ⟪ (T * T†) v, v ⟫_ℂ : by {rw lem_7_20_1_a, exact hT}
--   ...            =  ⟪ T ((T†) v), v ⟫_ℂ : by {rw comp_eq_mul}
--   ...            = ⟪ (T† ) v, (T† ) v ⟫_ℂ : by {rw linear_map.adjoint_inner_right}
--   ...            = ∥ (T†) v ∥^2 : by {rw inner_self_eq_norm_sq_to_K},
-- end


-- lemma lem_7_20_2_a (T : Lℂ^n) (v : ℂ^n) (h : (∥T v∥^2 : ℂ) = (∥(T†) v∥^2 : ℂ)) : ⟪(T * (T† )) v - ((T† * T) v), v ⟫_ℂ = 0 :=
-- begin
--   calc ⟪(T * (T†)) v - ((T† * T) v), v ⟫_ℂ = ⟪(T * (T†)) v, v ⟫_ℂ  - ⟪((T† * T) v), v ⟫_ℂ : by {rw inner_sub_left,}
--   ...                                      = ⟪ T (T† v), v⟫_ℂ - ⟪ T† (T v), v⟫_ℂ : by {rw [comp_eq_mul, comp_eq_mul]}
--   ...                                      = ⟪ T† v, T† v⟫_ℂ - ⟪ T v , T v ⟫_ℂ : by {rw linear_map.adjoint_inner_right, rw linear_map.adjoint_inner_left}
--   ...                                      = ∥ T† v ∥^2 - ∥ T v∥^2 : by {rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]}
--   ...                                      = 0 : by {rw h, exact sub_self _},
-- end

-- lemma lem_7_20_2_b(T : Lℂ^n): (T * T†) - (T† * T) = ((T * T† ) - (T† * T))† :=
-- begin
--   simp,
--   rw mul_adjoint,
--   rw mul_adjoint,
--   rw linear_map.adjoint_adjoint,
-- end

-- lemma lem_7_20_2_c (T : Lℂ^n) (h : ∀ v : ℂ^n, ⟪(T * (T† )) v - ((T† * T) v), v ⟫_ℂ = 0 ) : is_normal T :=
-- begin
--   rw is_normal,
--   rw ← sub_eq_zero,
--   have : (T * T†) - (T† * T) = 0 :=
--   begin
--     exact lem_7_16 _ (lem_7_20_2_b T) h,
--   end,
--   exact this,
-- end

-- lemma lem_7_20 (T : Lℂ^n) :
--   (is_normal T) ↔
--   ∀ v : ℂ^n,
--     (∥T v∥^2 : ℂ) = (∥(T†) v∥^2 : ℂ) :=
--   begin
--     split,
--     intros hT v,
--     exact lem_7_20_1_b T hT v,
--     intro h,
--     apply lem_7_20_2_c,
--     intro v,
--     apply lem_7_20_2_a,
--     exact h v,
--   end


-- example (u v : ℂ^ n) : ⟪ u , u ⟫_ℂ = ∥ u ∥^2 :=
-- begin
--   rw inner_self_eq_norm_sq_to_K,
-- end

-- lemma lem_7_21 (T : Lℂ^n)
--   (μ : ℂ) (v : ℂ^n)
--   (hT : is_normal T) (hv : T.has_eigenvector μ v) :
--   module.End.has_eigenvector (T.adjoint) (conj μ) v :=
-- begin
--   sorry,
-- end

-- lemma lem_7_22 (T : Lℂ^n)
--   (μ₁ μ₂ : ℂ) (v₁ v₂ : ℂ^n)
--   (hT : is_normal T) (hμ₁ : T.has_eigenvector μ₁ v₁) (hμ₂ : T.has_eigenvector μ₂ v₂)
--   (hneq : μ₁ ≠ μ₂) : ⟪v₁,v₂⟫_ℂ = 0 :=
-- begin
--   sorry,
-- end