import analysis.inner_product_space.adjoint
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum
import analysis.normed_space.pi_Lp

variable n : ℕ
def C : Type := euclidean_space ℂ (fin n)

notation `C` n := euclidean_space ℂ (fin n)

#check C n

example (v : C n) : v = v :=
begin
  exact rfl,
end


lemma inner_with_all_eq_zero_eq_zero (v : C n) : (∀ u : C n, ⟪u, v⟫_ℂ = 0) → v = 0 :=
begin
  intro h,
  by_contra',
  specialize h v,
  rw inner_self_eq_zero at h,
  exact this h,
end
