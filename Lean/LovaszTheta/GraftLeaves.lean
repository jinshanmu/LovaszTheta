module

public import LovaszTheta.RootedGraft
public import LovaszTheta.TreeRankPartition

/-!
# Leaves and paths in a grafted tree

Every proper child of the new root is an old root. With a
nonempty family the graft has exactly the disjoint union of the
old leaves, and the leaf residues at old nodes are unchanged.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

variable {I : Type*} (S : I → RootedTree) [Fintype I] (hI : Fintype.card I ≠ 1)

/-- The inclusion of a child's vertex set. -/
noncomputable def graftEmbedding (i : I) : (S i).Node ↪ (graft S hI).Node :=
  ⟨fun v ↦ graftNodeEquiv S hI (some ⟨i,v⟩), fun _ _ he ↦
    eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj ((graftNodeEquiv S hI).injective he))).2⟩

lemma graftEmbedding_apply (i : I) (v : (S i).Node) :
    graftEmbedding S hI i v = graftNodeEquiv S hI (some ⟨i,v⟩) := rfl

/-- The inclusion of the old roots. -/
noncomputable def graftRootEmbedding : I ↪ (graft S hI).Node :=
  ⟨fun i ↦ graftEmbedding S hI i (S i).root, fun _ _ he ↦
    congrArg Sigma.fst (Option.some.inj ((graftNodeEquiv S hI).injective he))⟩

lemma graftRootEmbedding_apply (i : I) :
    graftRootEmbedding S hI i = graftEmbedding S hI i (S i).root := rfl

lemma graftEmbedding_ne_root (i : I) (v : (S i).Node) :
    graftEmbedding S hI i v ≠ (graft S hI).root := by
  intro he
  have h := (graftNodeEquiv S hI).injective (show
    graftNodeEquiv S hI (some ⟨i,v⟩) = graftNodeEquiv S hI none from he)
  cases h

lemma graft_parent_old (i : I) (v : (S i).Node) (hv : v ≠ (S i).root) :
    (graft S hI).parent (graftEmbedding S hI i v) =
      graftEmbedding S hI i ((S i).parent v) := by
  simp only [graftEmbedding_apply, graft_parent_nodeEquiv, graftParent, ite_eq_right hv]

lemma graft_children_root :
    (graft S hI).children (graft S hI).root = univ.map (graftRootEmbedding S hI) := by
  ext w
  obtain ⟨u,rfl⟩ := (graftNodeEquiv S hI).surjective w
  rw [(graft S hI).mem_children_iff, graft_parent_nodeEquiv, ← graftNodeEquiv_none S hI,
    (graftNodeEquiv S hI).injective.ne_iff, (graftNodeEquiv S hI).injective.eq_iff,
    graftProperChild_root_iff, mem_map]
  simp only [mem_univ, true_and, graftRootEmbedding_apply, graftEmbedding_apply,
    (graftNodeEquiv S hI).injective.eq_iff, eq_comm]

lemma graft_children_old (i : I) (v : (S i).Node) :
    (graft S hI).children (graftEmbedding S hI i v) = ((S i).children v).map (graftEmbedding S hI i) := by
  ext w
  obtain ⟨u,rfl⟩ := (graftNodeEquiv S hI).surjective w
  simp only [(graft S hI).mem_children_iff, mem_map, graftEmbedding_apply,
    graft_parent_nodeEquiv, (graftNodeEquiv S hI).injective.ne_iff, (graftNodeEquiv S hI).injective.eq_iff,
    graftProperChild_some_iff, (S i).mem_children_iff, ← and_assoc, eq_comm (a := u)]

private lemma isLeaf_iff_children_eq_empty (T : RootedTree) (v : T.Node) :
    (∀ u, T.parent u = v → u = v) ↔ T.children v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [T.mem_children_iff, not_and]
  exact ⟨fun h u hne hp ↦ hne (h u hp), fun h u hp ↦ by by_contra hn; exact h u hn hp⟩

lemma graft_isLeaf_old (i : I) (v : (S i).Node) :
    (∀ u, (graft S hI).parent u = graftEmbedding S hI i v → u = graftEmbedding S hI i v) ↔
      ∀ u, (S i).parent u = v → u = v := by
  rw [isLeaf_iff_children_eq_empty, graft_children_old, map_eq_empty, isLeaf_iff_children_eq_empty]

lemma graft_root_not_leaf [Nonempty I] :
    ¬∀ u, (graft S hI).parent u = (graft S hI).root → u = (graft S hI).root := by
  rw [isLeaf_iff_children_eq_empty, graft_children_root, map_eq_empty]
  exact univ_nonempty.ne_empty

/-- Grafting a nonempty family does not add a leaf. -/
noncomputable def graftLeafEquiv [Nonempty I] : (Σ i, (S i).Leaf) ≃ (graft S hI).Leaf := by
  refine Equiv.ofBijective (fun a ↦ ⟨graftEmbedding S hI a.1 a.2.val,
    (graft_isLeaf_old S hI a.1 a.2.val).mpr a.2.property⟩) ⟨?_,?_⟩
  · rintro ⟨i,u⟩ ⟨j,v⟩ he
    have e : some (⟨i,u.val⟩ : Σ i, (S i).Node) = some ⟨j,v.val⟩ :=
      (graftNodeEquiv S hI).injective (congrArg Subtype.val he)
    have hij := congrArg Sigma.fst (Option.some.inj e)
    change i = j at hij
    subst j
    have huv : u = v := Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj e)).2)
    rw [huv]
  · rintro ⟨v,hv⟩
    obtain ⟨w,rfl⟩ := (graftNodeEquiv S hI).surjective v
    rcases w with _ | ⟨i,w⟩
    · exact (graft_root_not_leaf S hI hv).elim
    · exact ⟨⟨i,⟨w,(graft_isLeaf_old S hI i w).mp hv⟩⟩,rfl⟩

omit [Fintype I] in
private lemma iterate_graftParent_some (i : I) (u : (S i).Node) (k : ℕ) :
    (graftParent S)^[k] (some ⟨i,u⟩) = none ∨
    (graftParent S)^[k] (some ⟨i,u⟩) = some ⟨i, ((S i).parent^[k]) u⟩ := by
  induction k with
  | zero => exact Or.inr rfl
  | succ k ih =>
    rcases ih with h | h
    · exact Or.inl (by rw [Function.iterate_succ_apply', h]; rfl)
    · rw [Function.iterate_succ_apply', h, Function.iterate_succ_apply' (f := (S i).parent)]
      by_cases he : ((S i).parent^[k]) u = (S i).root
      · exact Or.inl (by simp only [graftParent, ite_eq_left he])
      · exact Or.inr (by simp only [graftParent, ite_eq_right he])

lemma graft_ancestor_old_iff {i j : I} {u : (S i).Node} {v : (S j).Node} :
    (graft S hI).IsAncestor (graftEmbedding S hI i u) (graftEmbedding S hI j v) ↔
      ∃ h : j = i, (S i).IsAncestor u (h ▸ v) := by
  constructor
  · rintro ⟨k,hk⟩
    have hs : Function.Semiconj (graftNodeEquiv S hI) (graftParent S) (graft S hI).parent :=
      fun z ↦ (graft_parent_nodeEquiv S hI z).symm
    change ((graft S hI).parent^[k]) (graftNodeEquiv S hI (some ⟨j,v⟩)) =
      graftNodeEquiv S hI (some ⟨i,u⟩) at hk
    rw [← hs.iterate_right k] at hk
    have he := (graftNodeEquiv S hI).injective hk
    rcases iterate_graftParent_some S j v k with h | h
    · rw [h] at he
      cases he
    · rw [h] at he
      have hji := congrArg Sigma.fst (Option.some.inj he)
      change j = i at hji
      subst j
      exact ⟨rfl,k,eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj he)).2⟩
  · rintro ⟨rfl,k,hk⟩
    induction k generalizing v with
    | zero =>
      have he : v = u := hk
      subst v
      exact (graft S hI).isAncestor_refl _
    | succ k ih =>
      by_cases hv : v = (S j).root
      · rw [hv, Function.iterate_fixed (S j).parent_root] at hk
        rw [hv, hk]
        exact (graft S hI).isAncestor_refl _
      · rw [Function.iterate_succ_apply] at hk
        have he := (graft S hI).isAncestor_parent (graftEmbedding S hI j v)
        rw [graft_parent_old S hI j v hv] at he
        exact (ih hk).trans he

lemma graft_mem_descendantLeaves [Nonempty I] (i : I) (v : (S i).Node)
    (j : I) (u : (S j).Leaf) :
    graftLeafEquiv S hI ⟨j,u⟩ ∈ (graft S hI).descendantLeaves (graftEmbedding S hI i v) ↔
      ∃ h : j = i, (h ▸ u) ∈ (S i).descendantLeaves v := by
  rw [(graft S hI).mem_descendantLeaves_iff]
  change (graft S hI).IsAncestor (graftEmbedding S hI i v) (graftEmbedding S hI j u.val) ↔ _
  rw [graft_ancestor_old_iff]
  constructor
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,((S j).mem_descendantLeaves_iff _ _).mpr h⟩
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,((S j).mem_descendantLeaves_iff _ _).mp h⟩

/-- The graft leaf assignment restricts to an assignment in each child. -/
theorem graft_residue_old [Nonempty I] {n : ℕ} (a : (graft S hI).Leaf → ZMod n) (i : I) (v : (S i).Node) :
    (graft S hI).residue a (graftEmbedding S hI i v) =
      (S i).residue (fun u ↦ a (graftLeafEquiv S hI ⟨i,u⟩)) v := by
  let e : (S i).Leaf ↪ (graft S hI).Leaf :=
    ⟨fun u ↦ graftLeafEquiv S hI ⟨i,u⟩, fun _ _ he ↦
      eq_of_heq (Sigma.mk.inj_iff.mp ((graftLeafEquiv S hI).injective he)).2⟩
  have hMap : (graft S hI).descendantLeaves (graftEmbedding S hI i v) = ((S i).descendantLeaves v).map e := by
    ext w
    obtain ⟨⟨j,u⟩,rfl⟩ := (graftLeafEquiv S hI).surjective w
    rw [graft_mem_descendantLeaves S hI, mem_map]
    constructor
    · rintro ⟨rfl,hu⟩
      exact ⟨u,hu,rfl⟩
    · rintro ⟨z,hz,he⟩
      have hs : (⟨i,z⟩ : Σ i, (S i).Leaf) = ⟨j,u⟩ := (graftLeafEquiv S hI).injective he
      have hji := congrArg Sigma.fst hs.symm
      change j = i at hji
      subst j
      have hu : z = u := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      exact ⟨rfl,hu ▸ hz⟩
  rw [residue, hMap, sum_map]
  rfl

/-- The new root residue is the sum of the residues at the old roots. -/
theorem graft_residue_root [Nonempty I] {n : ℕ} (a : (graft S hI).Leaf → ZMod n) :
    (graft S hI).residue a (graft S hI).root =
      ∑ i, (S i).residue (fun u ↦ a (graftLeafEquiv S hI ⟨i,u⟩)) (S i).root := by
  simp only [residue, descendantLeaves_root]
  rw [← (graftLeafEquiv S hI).sum_comp]
  exact Fintype.sum_sigma _

end LovaszTheta.Circulant.RootedTree
