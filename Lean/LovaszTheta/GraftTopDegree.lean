module

public import LovaszTheta.GraftModeExpansion
public import LovaszTheta.GraftNormalizer

/-!
# The leading part of a grafted field

A Fourier term has top sign degree exactly when all its node
residues are nonzero and lie in distinct inversion classes.
Such terms are in bijection with the admissible assignments
of the new tree.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace LovaszTheta.Circulant.RootedTree

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n] (S : I → RootedTree)

lemma nodeCard_appendedResidue :
    Fintype.card (GraftNode S) = 1+∑ i, (S i).nodeCount := by
  simp only [Fintype.card_option,Fintype.card_sigma,Fintype.card_fin,add_comm]

/-- Applying the sign operator increases the degree by at most
one above the sum of the degrees of the factors. -/
lemma walshDegree_signOperator_treeProduct_eq_zero (k : ZMod n) {d : ℕ}
    (hd : 1+∑ i, (S i).nodeCount < d) :
    walshDegree d (fun x ↦ signOperator x (fun j ↦ ∏ i, (S i).field x j) k) = 0 := by
  have he : (fun x ↦ signOperator x (fun j ↦ ∏ i, (S i).field x j) k) =
      (∏ i, (S i).fieldNormalizer n) •
        ∑ a : ChildAssignments S n, (characterMode (childRootSum S a) k).re •
          residueSignProduct (appendedResidue S a) := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,signOperator_treeProduct_eq_sum]
  rw [he,map_smul,map_sum]
  suffices ∀ a : ChildAssignments S n, walshDegree d (residueSignProduct (appendedResidue S a)) = 0 by
    simp only [map_smul,this,smul_zero,sum_const_zero]
  intro a
  by_cases hZ : ∃ v, appendedResidue S a v = 0
  · rw [residueSignProduct_eq_zero _ hZ,map_zero]
  · push Not at hZ
    rw [residueSignProduct_eq_walsh _ hZ,walshDegree_walsh,ite_eq_right]
    apply Nat.ne_of_lt
    exact (card_oddSignSupport_le _).trans_lt ((nodeCard_appendedResidue S).symm ▸ hd)

variable (hI : Fintype.card I ≠ 1) [Nonempty I]

/-- A family of assignments on the children determines all leaf labels of the graft. -/
noncomputable def extendChildAssignments (a : ChildAssignments S n) :
    (graft S hI).Leaf → ZMod n := fun u ↦
  let v := (graftLeafEquiv S hI).symm u
  (a v.1).val v.2

omit [NeZero n] in
lemma extendChildAssignments_apply (a : ChildAssignments S n) (i : I) (u : (S i).Leaf) :
    extendChildAssignments S hI a (graftLeafEquiv S hI ⟨i,u⟩) = (a i).val u := by
  unfold extendChildAssignments
  rw [Equiv.symm_apply_apply]

omit [NeZero n] in
lemma residue_extendChildAssignments (a : ChildAssignments S n) (v : GraftNode S) :
    (graft S hI).residue (extendChildAssignments S hI a) (graftNodeEquiv S hI v) = appendedResidue S a v := by
  rcases v with _ | ⟨i,v⟩
  · rw [graftNodeEquiv_none,graft_residue_root]
    simp only [extendChildAssignments_apply,appendedResidue,childRootSum]
  · change (graft S hI).residue (extendChildAssignments S hI a) (graftEmbedding S hI i v) = _
    rw [graft_residue_old]
    simp only [extendChildAssignments_apply,appendedResidue]

/-- Restriction of an admissible graft assignment remains admissible in every child. -/
noncomputable def restrictGraftAssignment (b : (graft S hI).Assignment n) : ChildAssignments S n :=
  fun i ↦ ⟨fun u ↦ b.val (graftLeafEquiv S hI ⟨i,u⟩), by
    have hr (v : (S i).Node) := graft_residue_old S hI b.val i v
    have hn (v : (S i).Node) : (S i).residue (fun u ↦ b.val (graftLeafEquiv S hI ⟨i,u⟩)) v ≠ 0 := by
      rw [← hr]
      exact b.property.choose _
    refine ⟨hn,fun v w he ↦ (graftEmbedding S hI i).injective (b.property.choose_spec ?_)⟩
    rw [inversionClass_eq_iff] at he ⊢
    rwa [hr,hr]⟩

omit [NeZero n] in
lemma extend_restrictGraftAssignment (b : (graft S hI).Assignment n) :
    extendChildAssignments S hI (restrictGraftAssignment S hI b) = b.val := by
  funext u
  obtain ⟨⟨i,v⟩,rfl⟩ := (graftLeafEquiv S hI).surjective u
  rw [extendChildAssignments_apply]
  rfl

/-- Exactly the jointly admissible child assignments give the
admissible leaf assignments at top degree. -/
noncomputable def graftAssignmentEquiv :
    {a : ChildAssignments S n // (graft S hI).Admissible (extendChildAssignments S hI a)} ≃
      (graft S hI).Assignment n where
  toFun a := ⟨extendChildAssignments S hI a.val,a.property⟩
  invFun b := ⟨restrictGraftAssignment S hI b,by
    rw [extend_restrictGraftAssignment]; exact b.property⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext u
    exact extendChildAssignments_apply S hI a.val i u
  right_inv b := Subtype.ext (extend_restrictGraftAssignment S hI b)

lemma RootedTree_graft_signSupport (a : ChildAssignments S n)
    (ha : (graft S hI).Admissible (extendChildAssignments S hI a))
    (hZ : ∀ v, appendedResidue S a v ≠ 0) :
    oddSignSupport (fun v ↦ inversionClass (appendedResidue S a v) (hZ v)) =
      (graft S hI).signSupport ⟨extendChildAssignments S hI a,ha⟩ := by
  let b : (graft S hI).Assignment n := ⟨extendChildAssignments S hI a,ha⟩
  let g := (graftNodeEquiv S hI).toEmbedding.trans ((graft S hI).classEmbedding b)
  have h (v : GraftNode S) :
      inversionClass (appendedResidue S a v) (hZ v) = g v := by
    apply (inversionClass_eq_iff (hZ v) (ha.choose (graftNodeEquiv S hI v))).mpr
    exact Or.inl (residue_extendChildAssignments S hI a v).symm
  rw [funext h,oddSignSupport_eq_map]
  unfold g signSupport
  rw [← Finset.map_map]
  congr 1
  exact Finset.map_univ_equiv _

private lemma walshDegree_appended (a : ChildAssignments S n) (k : ZMod n) :
    walshDegree (graft S hI).nodeCount ((characterMode (childRootSum S a) k).re •
      residueSignProduct (appendedResidue S a)) =
      if h : (graft S hI).Admissible (extendChildAssignments S hI a) then
        (characterMode (childRootSum S a) k).re •
          walsh ((graft S hI).signSupport ⟨_,h⟩) else 0 := by
  rw [map_smul]
  let G := graft S hI
  let b := extendChildAssignments S hI a
  by_cases hNZ : ∀ v, appendedResidue S a v ≠ 0
  · rw [residueSignProduct_eq_walsh _ hNZ]
    let f (v : GraftNode S) := inversionClass (appendedResidue S a v) (hNZ v)
    change (characterMode (childRootSum S a) k).re • walshDegree G.nodeCount (walsh (oddSignSupport f)) = _
    by_cases hA : G.Admissible b
    · rw [dite_eq_left hA,RootedTree_graft_signSupport S hI a hA hNZ,walshDegree_walsh,signSupport_card,ite_eq_left rfl]
    · have hi : ¬Function.Injective f := fun he ↦ hA (by
        have hn (v : G.Node) : G.residue b v ≠ 0 := by
          obtain ⟨w,rfl⟩ := (graftNodeEquiv S hI).surjective v
          rw [residue_extendChildAssignments]
          exact hNZ w
        refine ⟨hn,fun u v huv ↦ ?_⟩
        obtain ⟨u,rfl⟩ := (graftNodeEquiv S hI).surjective u
        obtain ⟨v,rfl⟩ := (graftNodeEquiv S hI).surjective v
        apply congrArg (graftNodeEquiv S hI)
        apply he
        rw [inversionClass_eq_iff,residue_extendChildAssignments,residue_extendChildAssignments] at huv
        exact (inversionClass_eq_iff _ _).mpr huv)
      have hlt : (oddSignSupport f).card < G.nodeCount := card_oddSignSupport_lt_of_not_injective f hi
      rw [dite_eq_right hA,walshDegree_walsh,ite_eq_right (Nat.ne_of_lt hlt),smul_zero]
  · have hZ : ∃ v, appendedResidue S a v = 0 := by push Not at hNZ; exact hNZ
    have hn : ¬G.Admissible b := fun he ↦ by
      obtain ⟨v,hv⟩ := hZ
      exact he.choose (graftNodeEquiv S hI v) ((residue_extendChildAssignments S hI a v).trans hv)
    rw [dite_eq_right hn,residueSignProduct_eq_zero _ hZ,map_zero,smul_zero]

/-- The homogeneous term of the product is the field of the graft,
with the ratio of the child normalization and the graft normalization. -/
theorem walshDegree_signOperator_treeProduct (k : ZMod n) :
    walshDegree (graft S hI).nodeCount (fun x ↦ signOperator x (fun j ↦ ∏ i, (S i).field x j) k) =
      ((∏ i, (S i).fieldNormalizer n) / (graft S hI).fieldNormalizer n) •
        (fun x ↦ (graft S hI).field x k) := by
  have he : (fun x ↦ signOperator x (fun j ↦ ∏ i, (S i).field x j) k) =
      (∏ i, (S i).fieldNormalizer n) •
        ∑ a : ChildAssignments S n, (characterMode (childRootSum S a) k).re •
          residueSignProduct (appendedResidue S a) := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,signOperator_treeProduct_eq_sum]
  rw [he,map_smul,map_sum]
  simp_rw [walshDegree_appended]
  funext x
  let G := graft S hI
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,field_eq_sum]
  have hN : G.fieldNormalizer n ≠ 0 := by
    have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    unfold fieldNormalizer
    exact inv_ne_zero (mul_ne_zero (Real.sqrt_ne_zero'.mpr (pow_pos hn _))
      (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos)))
  rw [← mul_assoc, div_mul_cancel₀ _ hN]
  congr 1
  let P (a : ChildAssignments S n) := G.Admissible (extendChildAssignments S hI a)
  rw [← (graftAssignmentEquiv S hI).sum_comp]
  simp only [dite_apply,Pi.zero_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_dite, sum_const_zero, add_zero]
  let e : ↑((univ : Finset (ChildAssignments S n)).filter P) ≃ {a // P a} :=
    (Equiv.refl _).subtypeEquiv fun a ↦ by simp
  refine Fintype.sum_equiv e _ _ fun a ↦ ?_
  have hR := residue_extendChildAssignments S hI a.val none
  change G.residue (extendChildAssignments S hI a.val) G.root = childRootSum S a.val at hR
  rw [← hR]
  rfl

end LovaszTheta.Circulant.RootedTree
