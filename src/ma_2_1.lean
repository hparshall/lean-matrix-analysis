import analysis.inner_product_space.pi_L2
import linear_algebra.dimension
import linear_algebra.matrix
import linear_algebra.unitary_group

open_locale big_operators matrix

variables {F m n: Type*}
  [is_R_or_C F]
  [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  [has_lt m] [has_lt n]

theorem thm_2_1_2 (v : n → (euclidean_space F m)) (hon : (orthonormal F v)) :
linear_independent F v := orthonormal.linear_independent hon

def is_unitary (A : matrix n n F) := Aᴴ ⬝ A = 1

def is_orthogonal (A : matrix n n ℝ) := Aᵀ ⬝ A = 1

lemma eq_0_5 (A : matrix n n F) (B : matrix n n F) : B ⬝ A = 1 ↔ A ⬝ B = 1 :=
begin
  apply matrix.mul_eq_one_comm,
end

theorem thm_2_1_4_a_b (A : matrix n n F) : is_unitary A ↔ (is_unit A) ∧ (A⁻¹ = Aᴴ) :=
begin
  split,
  intro h,
  split,
  rw is_unit,
  use A,
  exact Aᴴ,
  simp,
  rw eq_0_5,
  exact h,
  exact h,
  simp,
  apply matrix.inv_eq_left_inv _,
  exact h,
  intro h,
  cases h with h1 h2,
  rw is_unitary,
  rw ← h2,
  rw matrix.is_unit_iff_is_unit_det at h1,
  apply matrix.nonsing_inv_mul A h1,
end

theorem thm_2_1_4_b_c (A : matrix n n F) : (is_unit A) ∧ (A⁻¹ = Aᴴ) ↔ A ⬝ Aᴴ = 1 :=
begin
  split,
  intro h,
  rw eq_0_5,
  cases h with h1 h2,
  rw ← h2,
  rw matrix.is_unit_iff_is_unit_det at h1,
  apply matrix.nonsing_inv_mul A h1,
  intro h,
  split,
  rw is_unit,
  use A,
  use Aᴴ,
  simp,
  exact h,
  simp,
  rw eq_0_5,
  exact h,
  simp,
  apply matrix.inv_eq_right_inv h,
end

theorem thm_2_1_4_c_d (A : matrix n n F) : (A ⬝ Aᴴ = 1) ↔ is_unitary Aᴴ :=
begin
  split,
  intro h,
  rw is_unitary,
  simp,
  exact h,
  rw is_unitary,
  simp,
end

def cols (A : matrix m n F) :=
  λ (i : n), (id (Aᵀ i) : (euclidean_space F m))

def rows (A : matrix m n F) :=
  λ (i : m), (id (A i) : (euclidean_space F n))

def has_orthonormal_cols (A : matrix m n F) :=
  orthonormal F (cols A)

lemma entrywise_unitary (A : matrix n n F) (h: is_unitary A) : (∀ (i : n) (j : n), (Aᴴ ⬝ A) i j =  ite (i = j) 1 0) :=
begin
  rw is_unitary at h,
  rw ← matrix.ext_iff at h,
  intros i j,
  rw ← matrix.one_apply,
  apply h,
end

lemma entrywise_inner (A : matrix m n F) : ∀ i j : n, inner (cols A i) (cols A j) = (Aᴴ ⬝ A) i j :=
begin
  intros i j,
  ring,
end

theorem thm_2_1_4_a_e (A : matrix n n F) : is_unitary A ↔ has_orthonormal_cols A :=
begin
  split,
  intro h,
  rw has_orthonormal_cols,
  rw orthonormal_iff_ite,
  apply entrywise_unitary A,
  exact h,
  intro h,
  rw has_orthonormal_cols at h,
  rw orthonormal_iff_ite at h,
  rw is_unitary,
  ext,
  specialize h i j,
  have fact₁ : inner (cols A i) (cols A j) = (Aᴴ ⬝ A) i j, by apply entrywise_inner,
  rw ← fact₁,
  rw matrix.one_apply,
  exact h,
end

def is_isometry (A : matrix n n F) :=
  ∀ (x : (euclidean_space F n)), ∥x∥^2 = ∥ (id (matrix.to_lin' A x) : (euclidean_space F n) ) ∥^2

theorem thm_2_1_4_a_g (A : matrix n n F) : is_unitary A ↔ is_isometry A :=
begin
  sorry,
end

def is_similar_to (A B : matrix n n F) : Prop := ∃ P : matrix n n F, ((P⁻¹ ⬝ P = 1) ∧ (B = P * A * P⁻¹))


theorem thm_2_1_9 (A : matrix n n ℂ) [invertible A] : is_similar_to A⁻¹ Aᴴ ↔ ∃ (B : matrix n n ℂ), (is_unit B) ∧ A = B⁻¹ * Bᴴ :=
begin
  split,
  intro h,
  cases h with S hS,
  cases hS with hS₁ hS₂,
  have : S = Aᴴ ⬝ S ⬝ A,
  begin
    simp [hS₂],
    simp [matrix.mul_assoc],
    rw ←  matrix.mul_assoc S⁻¹ S  A,
    rw hS₁,
    simp,
  end,

  let Sθ : ℝ → matrix n n ℂ := λ (θ : ℝ), (matrix.scalar n (complex.exp(complex.I * θ))) ⬝ S,
  have fact₁: ∀(θ : ℝ), Sθ θ = Aᴴ ⬝ (Sθ θ) ⬝ A,
  begin
    sorry,
  end,
  have fact₂ : ∀(θ : ℝ), (Sθ θ)ᴴ = Aᴴ ⬝ (Sθ θ)ᴴ ⬝ A,
  begin
    sorry,
  end,
  let Hθ : ℝ → matrix n n ℂ := λ (θ : ℝ), Sθ θ + (Sθ θ)ᴴ,
  have fact₃ : ∀(θ : ℝ), Hθ θ = Aᴴ ⬝ (Hθ θ) ⬝ A :=
  begin
    intro θ,
    simp [Hθ],
    rw matrix.mul_add,
    rw matrix.add_mul,
    simp [fact₁ θ, fact₂ θ],
    rw ← fact₁ θ,
    simp,
    sorry,
  end,

  sorry,

  sorry,
end

variables A S : matrix n n ℂ
variable [S = Aᴴ ⬝ S ⬝ A]

noncomputable def Sθ : ℝ → matrix n n ℂ := λ (θ : ℝ), (matrix.scalar n (complex.exp(complex.I * θ))) ⬝ S
noncomputable def Hθ : ℝ → matrix n n ℂ := λ (θ : ℝ), (Sθ S θ) + (Sθ S θ)ᴴ

lemma fact₁: ∀(θ : ℝ), Sθ S θ = Aᴴ ⬝ (Sθ S θ) ⬝ A :=
begin
  sorry,
end
lemma fact₂ : ∀(θ : ℝ), (Sθ S θ)ᴴ = Aᴴ ⬝ (Sθ S θ)ᴴ ⬝ A :=
begin
  sorry,
end

#check fact₁
lemma fact₃ : ∀ (θ : ℝ), Hθ S θ = Aᴴ ⬝ (Hθ S θ) ⬝ A :=
begin
  intro θ,
  simp [Hθ],
  rw matrix.mul_add,
  rw matrix.add_mul,
  unfold Sθ,
  simp,
  rw ← _inst_8,
  rw ← fact₂ A S 0 (by simp),

end,


def is_upper_triangular (A : matrix n n F) :=
  ∀ (i j : n), j < i → (A i j = 0)

theorem thm_2_1_14_a (A : matrix m n F) (h : fintype.card m ≤ fintype.card n) :
  ∃ Q : (matrix m n F), ∃ R : (matrix n n F),
  (is_upper_triangular R)
    ∧(has_orthonormal_cols Q)
    ∧(A = Q ⬝ R)
    ∧(∀ i : n, is_R_or_C.re (R i i) ≥ 0)
    ∧(∀ i : n, is_R_or_C.im (R i i) = 0) :=
begin
  sorry
end

theorem thm_2_1_18 (X : matrix n n F) (Y : matrix n n F)
  (hx : has_orthonormal_cols X) (hy : has_orthonormal_cols Y) :
  ∃ (U : matrix n n F), (is_unitary U)∧(Y = U ⬝ X) :=
begin
  use Y ⬝ (X⁻¹),
  rw ← thm_2_1_4_a_e at hx,
  rw ← thm_2_1_4_a_e at hy,
  rw thm_2_1_4_a_b at hx,
  rw hx.2,
  rw ← thm_2_1_4_a_b at hx,
  split,
  rw is_unitary,
  simp,
  rw is_unitary at hy,
  rw matrix.mul_assoc,
  rw ← matrix.mul_assoc Yᴴ Y Xᴴ,
  rw hy,
  simp,
  rw ← thm_2_1_4_b_c,
  rw ← thm_2_1_4_a_b,
  exact hx,
  rw is_unitary at hx,
  rw matrix.mul_assoc,
  rw hx,
  simp,
end