import .gram
import .polar_decomp

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (T : Lℂ^n)

local notation `R` := (sqrt' T)

noncomputable def singular_values : (fin n → ℝ) := (gram_sa T).eigenvalues hn

noncomputable def e_basis : (basis (fin n) ℂ (ℂ^n)) := (gram_sa T).eigenvector_basis hn

example (T : Lℂ^n) (v : ℂ^n) : 1 = 2 :=
begin
  have h_fin : finite_dimensional.finrank ℂ (ℂ^n) = n :=
  begin
    simp only [fintype.card_fin, finrank_euclidean_space, eq_self_iff_true],
  end,
  -- let diag := inner_product_space.is_self_adjoint.diagonalization (r_sa),
  -- let blah := inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply (r_sa) (h_fin) v,
  -- let blah₂ := inner_product_space.is_self_adjoint.apply_eigenvector_basis (r_sa) (h_fin),
  have R_is_sa : is_sa R := R_sa T,
  let b := inner_product_space.is_self_adjoint.eigenvector_basis R_is_sa h_fin,
  have hb := inner_product_space.is_self_adjoint.eigenvector_basis_orthonormal R_is_sa h_fin,
  have : R v = ∑ (i : (fin n)), ⟪ (b i), v ⟫_ℂ • (R (b i)) :=
  begin
--     conv
--     begin
--       to_lhs,
--       rw onb_sum_repr b v hb,
--       skip,
--     end,
--     calc R (∑ (i : fin n), ⟪ b i, v ⟫_ℂ • (b i)) = ∑ (i : fin n), R (⟪ b i, v ⟫_ℂ • (b i)) : by {rw linear_map.map_sum}
--       ...                                        = ∑ (i : fin n), ⟪ b i, v ⟫_ℂ • R (b i) : by {simp only [is_R_or_C.inner_apply,
--  inner_product_space.is_self_adjoint.apply_eigenvector_basis,
--  pi_Lp.inner_apply,
--  eq_self_iff_true,
--  complex.coe_smul,
--  linear_map.map_smul,
--  finset.sum_congr]},
    sorry,
  end,
  let S := classical.some (lem_7_45 T),
  have hₛ : ∀ v : ℂ^n, (T v = S (R v)) := classical.some_spec (lem_7_45 T),
  have eq₂ : S (R v) = ∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • S (R (b i)) :=
  begin
    sorry,
--     calc S (R v) = S (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • R (b i)) : by {rw this}
--       ...        = S.to_linear_equiv.to_linear_map (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • R (b i)) : by {norm_cast}
--       ...        = ∑ (i : fin n), S (⟪ (b i), v ⟫_ℂ • R (b i)) : by {rw linear_map.map_sum, norm_cast}
--       ...        = (∑ (i : fin n), ⟪ (b i), v ⟫_ℂ • S (R (b i))) : by {simp only [is_R_or_C.inner_apply,
--  linear_isometry_equiv.map_smul,
--  inner_product_space.is_self_adjoint.apply_eigenvector_basis,
--  pi_Lp.inner_apply,
--  eq_self_iff_true,
--  complex.coe_smul,
--  finset.sum_congr]},
  end,
  rw ← hₛ at eq₂,

  conv at eq₂
  {
    to_rhs,
    congr,
    skip,
    funext,
    rw inner_product_space.is_self_adjoint.apply_eigenvector_basis R_is_sa,
    norm_cast,
    rw ← complex.coe_smul,
    rw linear_isometry_equiv.map_smulₛₗ S,
  },
  

  -- conv at eq₂
  -- {
  --   to_rhs,
  --   congr,
  --   skip,
  --   funext,
  --   rw ← hₛ,
  -- },


  -- have : ∀ μ : module.End.eigenvalues R, (r_sa.diagonalization) (R v) μ  = μ • ⇑(r_sa.diagonalization) v μ
  -- begin
  -- end
end

#check inner_product_space.is_self_adjoint.diagonalization (gram_sa T)

theorem svd : ∃ (f_basis : (basis (fin n) ℂ (ℂ^n))), ∀ (v : ℂ^n),
  T v = ∑ (i : (fin n)), (singular_values T i) • ⟪ v , e_basis T i ⟫_ℂ • (f_basis i) :=
begin

  sorry,
end