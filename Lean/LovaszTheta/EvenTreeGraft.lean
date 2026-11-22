module

public import LovaszTheta.EvenTreeTypes
public import LovaszTheta.FiniteMultiplicity
public import LovaszTheta.GraftIsomorphism

/-!
# Child multisets and unordered grafting

An unordered even-branching tree is determined by its even
multiset of child types. An empty multiset gives the leaf.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

namespace EvenPlaneTree

/-- Form a plane tree from an even number of even-branching children. -/
def mkChildren {j : ℕ} (hj : Even j) (c : Fin j → EvenPlaneTree) : EvenPlaneTree :=
  ⟨.mk j (fun i ↦ (c i).val), ⟨hj,fun i ↦ (c i).property⟩⟩

/-- An even arity cannot be one. -/
lemma card_fin_ne_one {j : ℕ} (hj : Even j) : Fintype.card (Fin j) ≠ 1 := by
  rw [Fintype.card_fin]
  obtain ⟨k,hk⟩ := hj
  omega

lemma rooted_mkChildren {j : ℕ} (hj : Even j) (c : Fin j → EvenPlaneTree) :
    (mkChildren hj c).rooted = RootedTree.graft (fun i ↦ (c i).rooted) (card_fin_ne_one hj) := rfl

/-- List the children's unordered types, keeping multiplicities. -/
noncomputable def childMultiset : EvenPlaneTree → Multiset EvenTreeType
  | ⟨.mk _ c,h⟩ => familyMultiset (fun i ↦ EvenTreeType.ofPlane ⟨c i,h.2 i⟩)

lemma childMultiset_mkChildren {j : ℕ} (hj : Even j) (c : Fin j → EvenPlaneTree) :
    (mkChildren hj c).childMultiset = familyMultiset (fun i ↦ EvenTreeType.ofPlane (c i)) := rfl

lemma childMultiset_even (t : EvenPlaneTree) : Even t.childMultiset.card := by
  obtain ⟨⟨j,c⟩,h⟩ := t
  change Even (familyMultiset (fun i : Fin j ↦ EvenTreeType.ofPlane ⟨c i,h.2 i⟩)).card
  rw [card_familyMultiset, Fintype.card_fin]
  exact h.1

lemma childMultiset_eq_iff (s t : EvenPlaneTree) :
    s.childMultiset = t.childMultiset ↔ Nonempty (s.rooted.Isomorphism t.rooted) := by
  obtain ⟨⟨j,c⟩,hs⟩ := s
  obtain ⟨⟨k,d⟩,ht⟩ := t
  let S (i : Fin j) : EvenPlaneTree := ⟨c i,hs.2 i⟩
  let T (i : Fin k) : EvenPlaneTree := ⟨d i,ht.2 i⟩
  change familyMultiset (fun i ↦ EvenTreeType.ofPlane (S i)) =
    familyMultiset (fun i ↦ EvenTreeType.ofPlane (T i)) ↔
      Nonempty ((mkChildren hs.1 S).rooted.Isomorphism (mkChildren ht.1 T).rooted)
  rw [rooted_mkChildren, rooted_mkChildren, familyMultiset_eq_iff]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨RootedTree.graftIsomorphism p fun i ↦
      ((EvenTreeType.ofPlane_eq_iff (S i) (T (p i))).mp (hp i).symm).some⟩
  · rintro ⟨e⟩
    exact ⟨RootedTree.graftChildPerm e, fun i ↦
      ((EvenTreeType.ofPlane_eq_iff _ _).mpr ⟨RootedTree.graftChildIso e i⟩).symm⟩

end EvenPlaneTree

namespace EvenTreeType

/-- The root's child multiset is invariant under rooted isomorphism. -/
noncomputable def children : EvenTreeType → {m : Multiset EvenTreeType // Even m.card} :=
  Quotient.lift (fun s ↦ ⟨s.childMultiset,s.childMultiset_even⟩) (fun s t e ↦
    Subtype.ext ((s.childMultiset_eq_iff t).mpr e))

lemma children_ofPlane (s : EvenPlaneTree) : (children (ofPlane s)).val = s.childMultiset := rfl

lemma children_injective : Function.Injective children := by
  intro S T h
  rw [← ofPlane_out S, ← ofPlane_out T]
  exact (ofPlane_eq_iff _ _).mpr (((Quotient.out S).childMultiset_eq_iff (Quotient.out T)).mp (by
    have hv := congrArg Subtype.val h
    rw [← ofPlane_out S, ← ofPlane_out T, children_ofPlane, children_ofPlane] at hv
    exact hv))

lemma children_surjective : Function.Surjective children := by
  rintro ⟨m,hm⟩
  have hLen : Even m.toList.length := by simpa using hm
  let c (i : Fin m.toList.length) : EvenPlaneTree := Quotient.out (m.toList[i])
  refine ⟨ofPlane (EvenPlaneTree.mkChildren hLen c), Subtype.ext ?_⟩
  rw [children_ofPlane, EvenPlaneTree.childMultiset_mkChildren]
  simpa only [c, ofPlane_out, Multiset.coe_toList] using familyMultiset_get m.toList

/-- The tree obtained by adjoining a root to the given children. -/
noncomputable def childrenEquiv : EvenTreeType ≃ {m : Multiset EvenTreeType // Even m.card} :=
  Equiv.ofBijective children ⟨children_injective, children_surjective⟩

/-- Graft an unordered multiset of children. -/
noncomputable def graft (m : Multiset EvenTreeType) (hm : Even m.card) : EvenTreeType :=
  childrenEquiv.symm ⟨m,hm⟩

lemma children_graft (m : Multiset EvenTreeType) (hm : Even m.card) :
    children (graft m hm) = ⟨m,hm⟩ :=
  childrenEquiv.apply_symm_apply _

lemma graft_isomorphism {I : Type*} [Fintype I] (f : I → EvenTreeType) (h : Even (Fintype.card I)) :
    Nonempty ((RootedTree.graft (fun i ↦ (f i).representative) (by obtain ⟨k,hk⟩ := h; omega)).Isomorphism
      (graft (familyMultiset f) (by rwa [card_familyMultiset])).representative) := by
  let G := graft (familyMultiset f) (by rwa [card_familyMultiset])
  let s : EvenPlaneTree := Quotient.out G
  have he : s.childMultiset = familyMultiset f := by
    rw [← children_ofPlane, ofPlane_out]
    exact congrArg Subtype.val (children_graft _ _)
  change Nonempty ((RootedTree.graft (fun i ↦ (f i).representative) _).Isomorphism s.rooted)
  obtain ⟨⟨j,c⟩,hs⟩ := s
  let S (i : Fin j) : EvenPlaneTree := ⟨c i,hs.2 i⟩
  change familyMultiset (fun i ↦ ofPlane (S i)) = familyMultiset f at he
  obtain ⟨p,hp⟩ := (familyMultiset_eq_iff _ _).mp he.symm
  change Nonempty ((RootedTree.graft (fun i ↦ (f i).representative) _).Isomorphism
    (EvenPlaneTree.mkChildren hs.1 S).rooted)
  rw [EvenPlaneTree.rooted_mkChildren]
  refine ⟨RootedTree.graftIsomorphism p fun i ↦ ?_⟩
  have hi : ofPlane (Quotient.out (f i)) = ofPlane (S (p i)) := (ofPlane_out _).trans (hp i).symm
  exact ((ofPlane_eq_iff _ _).mp hi).some

/-- Grafting adds one node to the sum of the child sizes. -/
theorem nodeCount_graft {I : Type*} [Fintype I] (f : I → EvenTreeType) (h : Even (Fintype.card I)) :
    (graft (familyMultiset f) (by rwa [card_familyMultiset])).nodeCount = 1+∑ i, (f i).nodeCount := by
  obtain ⟨e⟩ := graft_isomorphism f h
  rw [← representative_nodeCount, ← e.nodeCount_eq, RootedTree.graft_nodeCount]
  simp only [representative_nodeCount]

end EvenTreeType

end LovaszTheta.Circulant
