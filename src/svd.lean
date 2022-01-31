import .gram

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (T : Lℂ^n)

noncomputable def singular_values : (fin n → ℝ) := (gram_sa T).eigenvalues hn

noncomputable def e_basis : (basis (fin n) ℂ (ℂ^n)) := (gram_sa T).eigenvector_basis hn

theorem svd : ∃ (f_basis : (basis (fin n) ℂ (ℂ^n))), ∀ (v : ℂ^n),
  T v = ∑ (i : (fin n)), (singular_values T i) • ⟪ v , e_basis T i ⟫_ℂ • (f_basis i) :=
begin
  sorry,
end