import linear_algebra.linear_independent

variables {ι : Type*} {R : Type*} {M : Type*} {v : ι → M} {i j : ι}
[semiring R] [add_comm_monoid M] [module R M] [fintype ι] [decidable_eq ι]

lemma linear_independent_distinct (hli : (linear_independent R v)) : v i = v j ↔ i = j :=
begin
  sorry,
end