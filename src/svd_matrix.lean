import .svd
import data.matrix.basic
import algebra.star.basic
import .examples.std_basis_proof

-- -- theorem svd_matrix : ∃ U Σ V : matrix (fin n) (fin n) ℂ, A = U * Σ * V ∧ (Uᴴ = U ∧ Vᴴ = V) :=
-- -- sorry


variables {n : ℕ} (ι : Type*) [fintype ι] (A : matrix (fin n) (fin n) ℂ) {𝕜 : Type*} [is_R_or_C 𝕜]
open_locale matrix big_operators classical complex_conjugate

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- The vector given in euclidean space by being `1 : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
noncomputable def euclidean_space.single {𝕜 : Type*} {ι : Type*} [fintype ι] [is_R_or_C 𝕜] (i : ι) (a : 𝕜) :
 euclidean_space 𝕜 ι :=
  pi.single i a

@[simp] theorem euclidean_space.single_apply {𝕜 : Type*} {ι : Type*} [fintype ι]
  [is_R_or_C 𝕜] (i : ι) (a : 𝕜) (j : ι) :
  (euclidean_space.single i a) j = ite (j = i) a 0 :=
begin
  rw [euclidean_space.single, pi.single_apply i a j],
end

lemma euclidean_space.inner_single_left (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪euclidean_space.single i (a : 𝕜), v⟫ = conj a * (v i) :=
by simp [apply_ite conj]

lemma euclidean_space.inner_single_right (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪v, euclidean_space.single i (a : 𝕜)⟫ =  a * conj (v i) :=
by simp [apply_ite conj, mul_comm]

def matrix_to_lin_end (B : matrix (fin n) (fin n) ℂ) : (ℂ^n) → (ℂ^n) :=
begin
  let T := (id (B.to_lin') : (ℂ^n) → ℂ^n),
  exact T,
end

def matrix_eq_iff_lin_eq (A B : matrix (fin n) (fin n) ℂ) : A = B ↔ (id (A.to_lin') : Lℂ^n) = B.to_lin' :=
begin
  split,
  intro hₘ,
  rw hₘ,
  rw id.def,
  intro h,
  ext1,
  have key : ∀ D : (matrix (fin n) (fin n) ℂ), ((id (matrix.to_lin' D) : Lℂ^n ) (pi.basis_fun ℂ (fin n) j)) i = D i j :=
  begin
    intro D,
    simp only [pi.basis_fun_apply, id.def, matrix.mul_vec_std_basis, matrix.to_lin'_apply],
  end,
  rw ← key A,
  rw ← key B,
  rw h,
  rw id.def,
end

lemma basis_to_matrix_to_lin (b₁ b₂: basis (fin n) ℂ ℂ^n) (v : ℂ^n) (hb₁ : orthonormal ℂ b₁) (hb₂ : orthonormal ℂ b₂): matrix.to_lin' ((b₁.to_matrix b₂)ᴴ) v = ∑ (i : (fin n)), ⟪ b₂ i, v ⟫_ℂ • (b₁ i) :=
begin
  rw matrix.to_lin'_apply,
  conv
  begin
    to_rhs,
    congr,
    skip,
    funext,
    rw ← onb_coords_eq_inner b₂ _ _ hb₂,
  end, 
  -- rw ((b₁.to_matrix b₂)ᴴ ).mul_vec,
  apply basis.ext_elem b₁ _,
  intro j,
  have : (b₁.repr (∑ (i : fin n), ((b₂.repr) v i) • b₁ i)) j = (b₂.repr) v j :=
  begin
    rw linear_equiv.map_sum (b₁.repr) _,
    conv
    begin
      to_rhs,
      rw ← basis.sum_repr b₁ ( b₂.repr v ),
    end,
    unfold_coes,
    sorry,
    -- norm_cast,
    -- rw coe_fn_smul,
  end,
  rw this,
  -- simp only [matrix.dot_product],
  -- rw basis.to_matrix_transpose_apply,
  sorry,
end

lemma entries_are_application (A : matrix (fin n) (fin n) ℂ) (i j : fin n): A i j = (id (matrix.to_lin' A) : Lℂ^n) ((pi.basis_fun ℂ (fin n)) j) i :=
begin
  -- simp only [pi.basis_fun_apply, matrix.mul_vec_std_basis, matrix.to_lin'_apply],
  simp only [pi.basis_fun_apply, id.def, matrix.mul_vec_std_basis, matrix.to_lin'_apply],
end


lemma std_basis_to_matrix_apply (f : basis (fin n) ℂ ℂ^n) (i j : fin n) : (pi.basis_fun ℂ (fin n)).to_matrix f i j = f j i :=
begin
  sorry,
end

example : ∃ (U V : matrix (fin n) (fin n) ℂ) (s : (fin n) → ℝ), A = U * (matrix.diagonal ↑s) * Vᴴ ∧ (Uᴴ ⬝ U = 1) ∧ (Vᴴ ⬝ V = 1) :=
begin
  let T := (id(A.to_lin') : Lℂ^n),
  choose e f svd_T using (svd T),
  -- let std_basis := std_orthonormal_basis,
  -- let std_basis : basis (fin n) ℂ ℂ^n := basis.mk euclidean_space.single,
  let U : matrix (fin n) (fin n) ℂ := (fin_orthonormal_basis (finrank_euclidean_space_fin (ℂ^n)) ℂ (ℂ^n)).to_matrix ⇑f,
  let V := (std_orthonormal_basis ℂ (ℂ^n)).to_matrix ⇑e,
  use U,
  use V,
  use (singular_values T),

end

-- TODO:  Define singular values for matrices 

example : ∃ (U V : matrix (fin n) (fin n) ℂ) (s : (fin n) → ℝ), A = U * (matrix.diagonal ↑s) * Vᴴ ∧ (Uᴴ ⬝ U = 1) ∧ (Vᴴ ⬝ V = 1) :=
begin
  let T := (id(A.to_lin') : Lℂ^n),
  choose e f svd_T using (svd T),
  let std_basis : basis (fin n) ℂ ℂ^n := pi.basis_fun ℂ (fin n),
  let U := std_basis.to_matrix ⇑f,
  let V := std_basis.to_matrix ⇑e,
  use U,
  use V,
  use (singular_values T),
  split,
  simp only [U, V],
  simp only [matrix.mul_eq_mul],
  -- rw matrix_eq_iff_lin_eq,
  ext1,
  rw entries_are_application A i j,
  rw svd_T.2 _,
  have : (∑ (i : fin n), singular_values T i • inner (e i) ((pi.basis_fun ℂ (fin n)) j) • f i)
          = (∑ (i : fin n), singular_values T i • (star_ring_end ℂ (e i j)) • f i) :=
          begin
            conv
            begin
              to_lhs,
              congr,
              skip,
              funext,
              rw inner_std_basis_is_elem (e i) j,
            end
          end,
  rw this,
  clear this,

  rw matrix.mul_apply,
  simp only [matrix.mul_diagonal, matrix.conj_transpose_apply, finset.sum_congr, complex.star_def],
  have : ∑ (i : fin n), singular_values T i • (star_ring_end ℂ) (e i j) • f i 
      = ∑ (c : fin n), (λ i : (fin n), singular_values T i • (star_ring_end ℂ) (e i j) • f i) c :=
      begin
        simp only [eq_self_iff_true],
      end,
  rw this,
  rw @fintype.sum_apply _ _ _ _ _ i (λ i : (fin n), singular_values T i • (star_ring_end ℂ) (e i j) • f i),
  congr,
  simp?,
  ext1,
  rw std_basis_to_matrix_apply f i x,
  rw std_basis_to_matrix_apply e j x,
  have : (coe ((singular_values T)) : (fin n) → ℂ) x = ((singular_values T x) : ℂ)  := sorry,
  rw this,
  -- simp?,
  -- rw mul_comm (f x i) ((singular_values T) x),
  -- rw mul_assoc,
  ring,

  -- conv
  -- begin
  --   to_rhs,
  --   congr,
  --   skip,
  --   funext,
  --   rw std_basis.to_matrix_apply,
  --   rw std_basis.to_matrix_apply,
  -- end,
  -- simp only [pi.basis_fun_repr, finset.sum_congr],
  -- rw entries_are_application A i j,
  -- rw (svd_T.2 (pi.basis_fun ℂ (fin n) j)),
  -- apply fintype.sum_congr,
  -- rw fintype.sum_apply i _,
  -- have : (∑ (i : fin n), singular_values T i • inner (e i) ((pi.basis_fun ℂ (fin n)) j) • f i) = ∑ (c : fin n), (λ i : fin n, singular_values T i • inner (e i) ((pi.basis_fun ℂ (fin n)) j) • f i) c :=
  -- begin
  --   sorry,

  -- end,

  -- rw this,
  -- simp?,
  -- unfold matrix.dot_product,
  -- rw svd_T.2 x,


end
