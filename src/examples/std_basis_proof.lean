import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.normed_space.pi_Lp

variables {F M m : Type*}
[is_R_or_C F]
[fintype m]
[decidable_eq m]


noncomputable def std_basis
(F : Type*) (m : Type*)
[is_R_or_C F] [fintype m] [decidable_eq m] :=
(id (pi.basis_fun F m : basis m F (m → F)) : basis m F (euclidean_space F m))

def std_basis' (F m : Type*) [is_R_or_C F] [fintype m] [decidable_eq m]: m → (euclidean_space F m) := λ (i : m), (λ (j : m), ite (i = j) 1 0)

#check std_basis' F m

#check std_basis F m

lemma bm_on : orthonormal F (std_basis' F m) :=
begin
rw std_basis',
rw orthonormal,



split,
{
  
  intro i,
  rw euclidean_space.norm_eq,
  simp,
  have : (λ (i_1 : m), ∥ ite (i = i_1) (1:F) (0 : F) ∥^2) = λ (i_1 : m), ite (i = i_1) 1 0 :=
  begin
    ext,
    split_ifs,
    simp,
    simp,
  end,

  rw this,
  rw finset.sum_ite,
  simp,
  have : (finset.filter (eq i) finset.univ).card = 1 :=
  begin
    rw finset.card_eq_one,
    use i,
    ext,
    split,
    intro h,
    have : a = i :=
    begin
      simp at h,
      rw h,
    end,
    rw this,
    simp,
    intro h,
    simp at h,
    simp,
    rw h,
  end,
  rw this,
  simp,
},

{
  intros i_1 i_2 hij,
  unfold inner,
  simp,
  exact hij,
}
end
