import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp
import linear_algebra.basis
import .lemmas.ladr_7_lem

open_locale big_operators complex_conjugate matrix

variables {n : ℕ} (b : basis (fin n) ℂ ℂ^n) (v : ℂ^n) (hon : orthonormal ℂ b)

lemma onb_coords_eq_inner (i : fin n) (hon : orthonormal ℂ b) :
  (b.repr v) i = ⟪ b i, v ⟫_ℂ :=
begin
  rw orthonormal_iff_ite at hon,
  specialize hon i,
  conv
  begin
    to_rhs,
    rw ← b.sum_repr v,
    rw inner_sum,
    congr,
    skip,
    funext,
    dedup,
    rw inner_smul_right,
    rw hon,
    simp,
  end,
  rw finset.sum_ite,
  simp,
  rw finset.filter_eq,
  simp,
end

lemma onb_sum_repr (hon : orthonormal ℂ b):
  v = ∑ (i : (fin n)), ⟪b i, v⟫_ℂ • (b i) :=
begin
  conv
  begin
    congr,
    skip,
    congr,
    skip,
    funext,
    rw ← onb_coords_eq_inner b v i hon,
  end,
  symmetry,
  apply basis.sum_repr,
end