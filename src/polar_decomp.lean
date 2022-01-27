import .ladr_7_35
import .ladr_7
import .lemmas.ladr_7_lem

localized "postfix `†`:1000 := linear_map.adjoint" in src
variable {n : ℕ}
variable T : Lℂ^n

def is_isometry (S: Lℂ^n) : Prop := ∀ (v : ℂ^n), ∥ S v ∥ = ∥ v ∥


lemma adjoint_prod_sa : is_sa (T† * T) :=
begin
  intros x y,
  rw ← linear_map.adjoint_inner_right,
  rw mul_adjoint,
  rw linear_map.adjoint_adjoint,
end

noncomputable def sqrt' : Lℂ^n := sqrt (T† * T) (adjoint_prod_sa T)

--- This is a statement about the norm-squared. Later in the proof, they use just the norm,
--- I'm hoping we can stick to norm-squared, though, since it's easier to work with Lean-wise
lemma eq_7_46: ∀ (v : ℂ^n), ∥ T v ∥^2 = ∥ sqrt' T v ∥^2 :=
begin
  sorry,
end

--- The key step for S₁ being well-defined:
lemma lem_7_45_a : ∀ u v : ℂ^n, sqrt' T u = sqrt' T v → T u = T v :=
begin
  sorry,
end

#check linear_map.range T

--- These definitions so that the definition of S₁ doesn't time out :/
def range_sqrt : submodule ℂ ℂ^n := sorry
def range_T : submodule ℂ ℂ^n := sorry

--- We need to define this (which by virtue of its definition would prove that it is linear):
def S₁ : @range_sqrt n →ₗ[ℂ] @range_T n := sorry

--- I think we will need to show this (it won't be immediate from the defn):
--- Currently doesn't type check, because sqrt' T maps into C^n, and we want to land in range_sqrt, which is different

lemma lem_7_45_b :∀ v : ℂ^n, S₁ (sqrt' T v) = T v := sorry




lemma lem_7_45 : ∃ (S : Lℂ^n), (T = sqrt (T† * T) (adjoint_prod_sa T)) ∧ (is_isometry S) :=
begin
  sorry,
end


