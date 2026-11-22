module

public import LovaszTheta.EvenTreeGraft

/-!
# Branching probabilities of unordered trees

Fixing the root type fixes its arity and the multiplicities of its
child types. One may choose the child order and then independently
choose each child's ordered representative.
-/

@[expose] public section

open Finset
open scoped Classical ENNReal Nat

namespace LovaszTheta.Circulant.EvenTreeType

variable {j : ℕ} (hj : Even j) (f : Fin j → EvenTreeType)

/-- The unordered graft of an even tuple. -/
noncomputable def graftOfFn : EvenTreeType :=
  graft (familyMultiset f) (by simpa only [card_familyMultiset,Fintype.card_fin] using hj)

lemma children_graftOfFn : (children (graftOfFn hj f)).val = familyMultiset f :=
  congrArg Subtype.val (children_graft _ _)

lemma ofPlane_mkChildren_eq_graftOfFn_iff (c : Fin j → EvenPlaneTree) :
    ofPlane (EvenPlaneTree.mkChildren hj c) = graftOfFn hj f ↔
      familyMultiset (ofPlane ∘ c) = familyMultiset f := by
  rw [← children_injective.eq_iff]
  rw [Subtype.ext_iff, children_ofPlane, EvenPlaneTree.childMultiset_mkChildren, children_graftOfFn]
  rfl

/-- The plane representatives of a graft correspond to ordered
child representatives having the prescribed multiset of types. -/
noncomputable def graftPlaneEquiv :
    {c : Fin j → EvenPlaneTree // familyMultiset (ofPlane ∘ c) = familyMultiset f} ≃
      {t : EvenPlaneTree // ofPlane t = graftOfFn hj f} := by
  refine Equiv.ofBijective (fun c ↦ ⟨EvenPlaneTree.mkChildren hj c.val,
    (ofPlane_mkChildren_eq_graftOfFn_iff hj f c.val).mpr c.property⟩) ⟨?_,?_⟩
  · intro c d h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have he : (WType.mk j (fun i ↦ (c.val i).val) : PlaneTree) =
      WType.mk j (fun i ↦ (d.val i).val) := congrArg (fun t ↦ t.val.val) h
    have hSigma := congrArg (WType.toSigma (β := fun j : ℕ ↦ Fin j)) he
    exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2) i
  · rintro ⟨⟨⟨k,c⟩,hk⟩,he⟩
    have h' : familyMultiset (fun i : Fin k ↦ ofPlane ⟨c i,hk.2 i⟩) = familyMultiset f :=
      (congrArg (fun T ↦ (children T).val) he).trans (children_graftOfFn hj f)
    have hCard := congrArg Multiset.card h'
    simp only [card_familyMultiset, Fintype.card_fin] at hCard
    subst k
    let d (i : Fin j) : EvenPlaneTree := ⟨c i,hk.2 i⟩
    exact ⟨⟨d,h'⟩,rfl⟩

/-- After selecting an ordering, choose its individual representatives. -/
noncomputable def orderedChildRepresentativesEquiv :
    {c : Fin j → EvenPlaneTree // familyMultiset (ofPlane ∘ c) = familyMultiset f} ≃
      Σ g : FamilyOrdering f, ∀ i, {t : EvenPlaneTree // ofPlane t = g.val i} where
  toFun c := ⟨⟨ofPlane ∘ c.val,c.property⟩,fun i ↦ ⟨c.val i,rfl⟩⟩
  invFun g := ⟨fun i ↦ (g.2 i).val, by
    have he : (ofPlane ∘ fun i ↦ (g.2 i).val) = g.1.val := funext fun i ↦ (g.2 i).property
    rw [he,g.1.property]⟩
  left_inv := fun _ ↦ rfl
  right_inv g := by
    have ext {x y : FamilyOrdering f} (he : x = y)
        (a : ∀ i, {t : EvenPlaneTree // ofPlane t = x.val i})
        (b : ∀ i, {t : EvenPlaneTree // ofPlane t = y.val i})
        (h : ∀ i, (a i).val = (b i).val) : HEq a b := by
      subst y
      exact heq_of_eq (funext fun i ↦ Subtype.ext (h i))
    have h : (ofPlane ∘ fun i ↦ (g.2 i).val) = g.1.val := funext fun i ↦ (g.2 i).property
    exact Sigma.ext (Subtype.ext h) (ext (Subtype.ext h) _ _ fun _ ↦ rfl)

/-- The unordered probability is the root probability times the
product of child probabilities and their multinomial ordering count. -/
theorem branchingProbability_graftOfFn (p : ℕ → ℝ≥0∞) :
    branchingProbability p (graftOfFn hj f) =
      (Fintype.card (FamilyOrdering f) : ℝ≥0∞) * (p j * ∏ i, branchingProbability p (f i)) := by
  let q (t : {t : EvenPlaneTree // ofPlane t = graftOfFn hj f}) := PlaneTree.weight p t.val.val
  change (∑' t,q t) = _
  let e := (orderedChildRepresentativesEquiv f).symm.trans (graftPlaneEquiv hj f)
  rw [← e.tsum_eq, tsum_sigma']
  have h (g : FamilyOrdering f) (c : ∀ i, {t : EvenPlaneTree // ofPlane t = g.val i}) :
      q (e ⟨g,c⟩) = p j * ∏ i, PlaneTree.weight p (c i).val.val := rfl
  have hSum (g : FamilyOrdering f) :
      (∑' c : ∀ i, {t : EvenPlaneTree // ofPlane t = g.val i}, q (e ⟨g,c⟩)) =
        p j * ∏ i, branchingProbability p (g.val i) := by
    simp only [h, ENNReal.tsum_mul_left]
    exact congrArg (p j * ·) (PlaneTree.tsum_product_fin
      (fun (i : Fin j) (c : {t : EvenPlaneTree // ofPlane t = g.val i}) ↦ PlaneTree.weight p c.val.val))
  have hProd (g : FamilyOrdering f) : (∏ i, branchingProbability p (g.val i)) =
      ∏ i, branchingProbability p (f i) := by
    obtain ⟨r,hr⟩ := (familyMultiset_eq_iff f g.val).mp g.property.symm
    exact (Fintype.prod_equiv r _ _ (fun i ↦ congrArg (branchingProbability p) (hr i).symm)).symm
  simp only [hSum, hProd, tsum_fintype, sum_const, nsmul_eq_mul, card_univ]

/-- The canonical listing of the child types of a tree. -/
noncomputable def childList (T : EvenTreeType) : List EvenTreeType := (children T).val.toList

lemma childList_even (T : EvenTreeType) : Even T.childList.length := by
  simpa [childList] using (children T).property

lemma graftOfFn_childList (T : EvenTreeType) :
    graftOfFn (childList_even T) (fun i : Fin T.childList.length ↦ T.childList[i]) = T := by
  apply children_injective
  apply Subtype.ext
  rw [children_graftOfFn,familyMultiset_get]
  exact Multiset.coe_toList _

lemma childList_nodeCount_lt (T : EvenTreeType) (i : Fin T.childList.length) :
    T.childList[i].nodeCount < T.nodeCount := by
  let g (i : Fin T.childList.length) := T.childList[i]
  have h := nodeCount_graft g (by simpa only [Fintype.card_fin] using childList_even T)
  change (graftOfFn (childList_even T) g).nodeCount = 1+∑ j, (g j).nodeCount at h
  rw [graftOfFn_childList] at h
  have hi : (g i).nodeCount ≤ ∑ j, (g j).nodeCount :=
    single_le_sum (f := fun j ↦ (g j).nodeCount) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
  change T.childList[i].nodeCount ≤ _ at hi
  omega

end LovaszTheta.Circulant.EvenTreeType
