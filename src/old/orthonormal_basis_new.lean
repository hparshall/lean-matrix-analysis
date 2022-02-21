import analysis.inner_product_space.projection
import analysis.normed_space.lp_space
import analysis.inner_product_space.l2_space
import analysis.inner_product_space.pi_L2

open is_R_or_C submodule filter
open_locale big_operators nnreal ennreal classical complex_conjugate

noncomputable theory


-- Currently just throwing in everything from hilbert_space, editing as necessary
-- Should be able to get rid of [complete_space E]
variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E] [fintype ι] 
variables {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y


variables (ι) (𝕜) (E)

def euclidean_space.single {𝕜 : Type*} {ι : Type*} [fintype ι] [is_R_or_C 𝕜] (i : ι) (a : 𝕜): euclidean_space 𝕜 ι := 
  lp.single 2 i (a : 𝕜)


theorem euclidean_space.single_apply {𝕜 : Type*} {ι : Type*} [fintype ι] [is_R_or_C 𝕜] (i : ι) (a : 𝕜) (j : ι) : 
  (euclidean_space.single i a) j = dite (j = i) (λ (h : j = i), a) (λ (h : ¬j = i), 0) :=
  begin
    rw euclidean_space.single,
    rw lp.single_apply,
    simp only [dite_eq_ite, eq_rec_constant, dif_ctx_congr],
  end

lemma euclidean_space.inner_single_left (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) : 
  ⟪ euclidean_space.single i (a : 𝕜), v ⟫ = star_ring_end 𝕜 a * (v i) :=
  begin
    simp only [is_R_or_C.inner_apply, pi_Lp.inner_apply, finset.sum_congr],
    rw euclidean_space.single,
    conv
    begin
      to_lhs,
      congr,
      skip,
      funext,
      rw lp.single_apply 2 i a x,
    end,
    simp only [dite_eq_ite, eq_rec_constant, dif_ctx_congr, finset.sum_congr],
    conv
    begin
      to_lhs,
      congr,
      skip,
      funext,
      rw apply_ite (star_ring_end 𝕜),
      rw @star_ring_end_apply _ _ _ (0 : 𝕜),
      rw star_zero,
      rw ite_mul,
    end,
    simp only [finset.mem_univ,
 if_true,
 mul_eq_mul_left_iff,
 zero_mul,
 true_or,
 eq_self_iff_true,
 finset.sum_ite_eq',
 ring_hom.map_eq_zero,
 finset.sum_congr],
  end

lemma euclidean_space.inner_single_right (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) : 
  ⟪ v, euclidean_space.single i (a : 𝕜) ⟫ =  a * (star_ring_end 𝕜) (v i) :=
  begin
    rw [← inner_conj_sym, euclidean_space.inner_single_left],
    rw star_ring_end_apply,
    rw star_mul',
    rw ← star_ring_end_apply,
    rw ← star_ring_end_apply,
    rw star_ring_end_self_apply,
  end

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching `euclidean_space`. -/
structure orthonormal_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι)

namespace orthonormal_basis

instance : inhabited (orthonormal_basis ι 𝕜 (euclidean_space 𝕜 ι)) :=
  ⟨of_repr (linear_isometry_equiv.refl 𝕜 (euclidean_space 𝕜 ι)) ⟩ 

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (orthonormal_basis ι 𝕜 E) (λ _, ι → E) := 
{
  coe := λ b i, b.repr.symm (euclidean_space.single i (1 : 𝕜))
}

@[simp] protected lemma repr_symm_single (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (euclidean_space.single i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_self (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = euclidean_space.single i (1:𝕜) :=
  begin
    rw [← b.repr_symm_single _ _ _, linear_isometry_equiv.apply_symm_apply],
  end

protected lemma repr_apply_apply (b : orthonormal_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  rw [← b.repr.inner_map_map (b i) v, b.repr_self _ _ _, euclidean_space.inner_single_left],
  simp only [one_mul, eq_self_iff_true, map_one],
end

@[simp] 
protected lemma orthonormal (b : orthonormal_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self _ _ _, b.repr_self _ _ _],
  rw euclidean_space.inner_single_left,
  rw euclidean_space.single_apply,
  simp only [mul_boole, dite_eq_ite, eq_self_iff_true, map_one],
end

variables {ι} {𝕜} {E}
variable {v : ι → E}

/-- An orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤): orthonormal_basis ι 𝕜 E :=
  orthonormal_basis.of_repr $
  basis.isometry_euclidean_of_orthonormal (basis.mk (orthonormal.linear_independent hon) hsp) 
  begin
    rw basis.coe_mk,
    exact hon,
  end


@[simp]
protected lemma coe_mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤) : 
  ⇑(orthonormal_basis.mk hon hsp) = v :=
begin
  ext i,
  show (orthonormal_basis.mk hon hsp).repr.symm _ = v i,
  simp only [basis.coe_isometry_euclidean_of_orthonormal_symm,
 orthonormal_basis.mk.equations._eqn_1,
 basis.coe_mk,
 basis.equiv_fun_symm_apply,
 finset.sum_congr],
 conv
 begin
   to_lhs,
   congr,
   skip,
   funext,
    rw euclidean_space.single_apply,
    rw dite_eq_ite,
  rw ite_smul,
 end,
  simp only [finset.mem_univ,
 if_true,
 eq_self_iff_true,
 one_smul,
 finset.sum_ite_eq',
 zero_smul,
 finset.sum_congr],
end


/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.basis.to_orthonormal_basis (b : basis ι 𝕜 E) (hb : orthonormal 𝕜 b) : 
  orthonormal_basis ι 𝕜 E := 
    orthonormal_basis.of_repr(basis.isometry_euclidean_of_orthonormal b hb)



end orthonormal_basis
