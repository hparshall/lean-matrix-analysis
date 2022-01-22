import analysis.inner_product_space.pi_L2
import linear_algebra.dimension
import linear_algebra.matrix
import .ma_2_1

open_locale big_operators matrix

variables {F m n: Type*}
  [is_R_or_C F]
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [has_lt m] [has_lt n]

def unitarily_similar (A : matrix n n F) (B : matrix n n F) :=
  ∃ U : matrix n n F, A = U ⬝ B ⬝ Uᴴ