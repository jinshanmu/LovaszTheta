module

public import LovaszTheta.GraftLeaves
public import LovaszTheta.SignModes
public import LovaszTheta.WalshDegree

/-!
# Fourier expansion after adjoining the root sign

Multiplying the child fields adds their root residues in the
Fourier mode. Applying the sign operator inserts the sign of
that sum. Every term is now a sign product on the graft nodes.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Circulant.RootedTree

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n] (S : I → RootedTree)

/-- A separate admissible assignment in each child of the family. -/
abbrev ChildAssignments (n : ℕ) := ∀ i, (S i).Assignment n

/-- The sum of the residues at the child roots. -/
noncomputable def childRootSum (a : ChildAssignments S n) : ZMod n :=
  ∑ i, (S i).residue (a i).val (S i).root

/-- The residues after inserting the new root. -/
noncomputable def appendedResidue (a : ChildAssignments S n) : GraftNode S → ZMod n
  | none => childRootSum S a
  | some ⟨i,v⟩ => (S i).residue (a i).val v

omit [NeZero n] in
lemma residueSignProduct_appendedResidue (a : ChildAssignments S n) (x : InversionClass n → Bool) :
    residueSignProduct (appendedResidue S a) x =
      epsilon x (childRootSum S a) * ∏ i, walsh ((S i).signSupport (a i)) x := by
  unfold residueSignProduct
  rw [Fintype.prod_option,Fintype.prod_sigma]
  simp only [appendedResidue,walsh_signSupport]

private lemma prod_rootMode (a : ChildAssignments S n) (k : ZMod n) :
    (∏ i, ZMod.stdAddChar (-((S i).residue (a i).val (S i).root * k))) =
      characterMode (childRootSum S a) k := by
  let r (i : I) := (S i).residue (a i).val (S i).root
  have h (s : Finset I) : (∏ i ∈ s, ZMod.stdAddChar (-(r i*k))) =
      ZMod.stdAddChar (-(∑ i ∈ s, r i*k)) := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => rw [prod_cons,sum_cons,ih,neg_add,AddChar.map_add_eq_mul]
  unfold characterMode childRootSum
  rw [sum_mul]
  exact h univ

/-- The complex child product factors into one Fourier mode for
each set of child assignments. -/
lemma ofReal_treeProduct (x : InversionClass n → Bool) :
    (fun k ↦ ((∏ i, (S i).field x k : ℝ) : ℂ)) =
      ((∏ i, ((S i).fieldNormalizer n : ℂ)) : ℂ) •
        ∑ a : ChildAssignments S n,
          (∏ i, (walsh ((S i).signSupport (a i)) x : ℂ)) • characterMode (childRootSum S a) := by
  funext k
  simp only [Complex.ofReal_prod,ofReal_field,fieldComplex,prod_mul_distrib,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  congr 1
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  rw [prod_mul_distrib,prod_rootMode,mul_comm]

/-- Applying the sign operator to a product of tree fields adds
the sign of the sum of the child residues. -/
theorem signOperator_treeProduct_eq_sum (x : InversionClass n → Bool) (k : ZMod n) :
    signOperator x (fun j ↦ ∏ i, (S i).field x j) k =
      (∏ i, (S i).fieldNormalizer n) *
        ∑ a : ChildAssignments S n, (characterMode (childRootSum S a) k).re *
          residueSignProduct (appendedResidue S a) x := by
  let K := (multiplier (fun s ↦ (epsilon x s : ℂ))).mulVecLin
  have hK (s : ZMod n) : K (characterMode s) = (epsilon x s : ℂ) • characterMode s :=
    multiplier_mulVec_characterMode _ _
  have he := signOperator_complexification x (fun j ↦ ∏ i, (S i).field x j)
  change (fun j ↦ (signOperator x (fun j ↦ ∏ i, (S i).field x j) j : ℂ)) =
    K (fun k ↦ ((∏ i, (S i).field x k : ℝ) : ℂ)) at he
  rw [ofReal_treeProduct S, map_smul, map_sum] at he
  simp_rw [map_smul,hK] at he
  have h := congrArg Complex.re (congrFun he k)
  simp only [Complex.ofReal_re, Pi.smul_apply, smul_eq_mul,Finset.sum_apply,← Complex.ofReal_prod] at h
  rw [h]
  simp only [Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,Complex.re_sum]
  congr 1
  apply sum_congr rfl
  intro a _
  rw [residueSignProduct_appendedResidue S]
  ring

end LovaszTheta.Circulant.RootedTree
