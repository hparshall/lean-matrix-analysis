import analysis.inner_product_space.pi_L2

notation `ℂ^` n := euclidean_space ℂ (fin n)

open_locale big_operators

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
  simp only [add_zero, finset.sum_const_zero, finset.filter_congr_decidable, finset.sum_congr],
  rw finset.filter_eq,
  simp only [finset.mem_univ, if_true, eq_self_iff_true, finset.sum_singleton, finset.sum_congr],
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