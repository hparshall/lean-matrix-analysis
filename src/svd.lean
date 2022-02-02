import .gram
import .polar_decomp

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (T : Lℂ^n)

noncomputable def singular_values : (fin n → ℝ) := (gram_sa T).eigenvalues hn

noncomputable def e_basis : (basis (fin n) ℂ (ℂ^n)) := (gram_sa T).eigenvector_basis hn


example (T : Lℂ^n) (v : ℂ^n) : 1 = 2 :=
begin
  cases (sqrt_gram T) with R hᵣ,
  cases hᵣ with r_sqs hᵣ,
  cases hᵣ with r_sa r_pos,
  have h_fin : finite_dimensional.finrank ℂ (ℂ^n) = n :=
  begin
    simp only [fintype.card_fin, finrank_euclidean_space, eq_self_iff_true],
  end,
  -- let diag := inner_product_space.is_self_adjoint.diagonalization (r_sa),
  let blah := inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply (r_sa) (h_fin) v,
  -- let blah₂ := inner_product_space.is_self_adjoint.apply_eigenvector_basis (r_sa) (h_fin),
  
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