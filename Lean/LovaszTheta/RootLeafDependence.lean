module

public import LovaszTheta.DescendantSupport

/-!
# Minimal dependencies involving the root row

The root together with all leaves is a minimal dependence.
The elimination identifies dependent selected rows by finding a
node whose leaves are covered by proper selected descendants.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

/-- A row set is minimally dependent when deletion of any nonempty
part leaves a row set of full rank. -/
def IsMinimalDependence (T : RootedTree) (A : Finset T.Node) : Prop :=
  leafRowRank T.leafRow A < A.card ∧
    ∀ B ⊂ A, leafRowRank T.leafRow B = B.card

lemma residualLeaves_eq_empty_iff (T : RootedTree) (A : Finset T.Node) (u : T.Node) :
    T.residualLeaves A u = ∅ ↔
      ∀ i ∈ T.descendantLeaves u, ∃ w ∈ A, i ∈ T.descendantLeaves w ∧ T.depth u < T.depth w := by
  constructor
  · intro h i hi
    have he : ¬∀ w ∈ A, i ∈ T.descendantLeaves w → T.depth w ≤ T.depth u := by
      intro hAll
      have hm : i ∈ T.residualLeaves A u := mem_filter.mpr ⟨hi, hAll⟩
      simp [h] at hm
    push Not at he
    exact he
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hLeaf, hMax⟩ := mem_filter.mp hi
    obtain ⟨w, hw, hiw, hLt⟩ := h i hLeaf
    exact (not_lt_of_ge (hMax w hw hiw)) hLt

lemma leafRowRank_eq_card_of_residual_nonempty (T : RootedTree) (A : Finset T.Node)
    (h : ∀ v ∈ A, (T.residualLeaves A v).Nonempty) :
    leafRowRank T.leafRow A = A.card := by
  rw [T.leafRowRank_eq_card_residual, nonemptyResidualRoles, filter_true_of_mem h]

lemma leafRowRank_lt_card_iff_residual_empty (T : RootedTree) (A : Finset T.Node) :
    leafRowRank T.leafRow A < A.card ↔ ∃ v ∈ A, T.residualLeaves A v = ∅ := by
  constructor
  · intro h
    by_contra! he
    rw [T.leafRowRank_eq_card_of_residual_nonempty A he] at h
    exact (lt_irrefl _) h
  · rintro ⟨v, hv, he⟩
    rw [T.leafRowRank_eq_card_residual]
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
    intro heq
    have hv' : v ∈ T.nonemptyResidualRoles A := heq.symm ▸ hv
    have hh := (mem_filter.mp hv').2
    rw [he] at hh
    exact not_nonempty_empty hh

/-- The nodes that are leaves. -/
noncomputable def leafNodes (T : RootedTree) : Finset T.Node :=
  (univ : Finset T.Leaf).map ⟨Subtype.val, Subtype.val_injective⟩

/-- The selected row set consisting of the root and every leaf. -/
noncomputable def rootLeafSet (T : RootedTree) : Finset T.Node :=
  insert T.root T.leafNodes

lemma mem_leafNodes_iff (T : RootedTree) (v : T.Node) :
    v ∈ T.leafNodes ↔ ∀ w, T.parent w = v → w = v := by
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_map.mp hv
    exact i.property
  · intro h
    exact mem_map.mpr ⟨⟨v, h⟩, mem_univ _, rfl⟩

lemma root_not_mem_leafNodes (T : RootedTree) (hT : 1 < T.nodeCount) :
    T.root ∉ T.leafNodes := by
  intro hRoot
  have hn : 0 < ((univ : Finset T.Node).erase T.root).card := by
    rw [card_erase_of_mem (mem_univ T.root), card_univ, Fintype.card_fin]
    omega
  obtain ⟨v, hv⟩ := card_pos.mp hn
  have hne : v ≠ T.root := (mem_erase.mp hv).1
  obtain ⟨w, hw, _⟩ := exists_child_ancestor (T.exists_iterate_parent_eq_root v) hne
  obtain ⟨hW, hPar⟩ := (T.mem_children_iff T.root w).mp hw
  exact hW ((T.mem_leafNodes_iff _).mp hRoot w hPar)

lemma card_rootLeafSet (T : RootedTree) (hT : 1 < T.nodeCount) :
    T.rootLeafSet.card = Fintype.card T.Leaf + 1 := by
  rw [rootLeafSet, card_insert_of_notMem (T.root_not_mem_leafNodes hT), leafNodes, card_map,
    card_univ]

/-- The root and all leaves form a minimal dependence in a nontrivial tree. -/
theorem isMinimalDependence_rootLeafSet (T : RootedTree) (hT : 1 < T.nodeCount) :
    T.IsMinimalDependence T.rootLeafSet := by
  have hRoot : T.root ∈ T.rootLeafSet := mem_insert_self _ _
  have hnRoot (i : T.Leaf) : i.val ≠ T.root := fun he ↦ T.root_not_mem_leafNodes hT
    (mem_map.mpr ⟨i, mem_univ _, he⟩)
  refine ⟨(T.leafRowRank_lt_card_iff_residual_empty _).mpr ⟨T.root, hRoot, ?_⟩, ?_⟩
  · apply (T.residualLeaves_eq_empty_iff _ _).mpr
    intro i _
    refine ⟨i.val, mem_insert_of_mem (mem_map.mpr ⟨i, mem_univ _, rfl⟩), ?_, ?_⟩
    · rw [T.descendantLeaves_leaf i]
      exact mem_singleton_self _
    · exact IsAncestor.depth_lt (T := T) (u := T.root) (v := i.val)
        (T.exists_iterate_parent_eq_root i.val) (hnRoot i).symm
  · intro B hB
    apply T.leafRowRank_eq_card_of_residual_nonempty
    intro u hu
    by_cases hU : u = T.root
    · subst u
      have hSub : ¬T.rootLeafSet ⊆ B := fun he ↦
        (Finset.ssubset_iff_subset_ne.mp hB).2 (Subset.antisymm hB.le he)
      obtain ⟨v, hv, hvB⟩ := Finset.not_subset.mp hSub
      have hvLeaf : v ∈ T.leafNodes := (mem_insert.mp hv).resolve_left fun he ↦ hvB (he.symm ▸ hu)
      obtain ⟨i, _, hi⟩ := mem_map.mp hvLeaf
      change i.val = v at hi
      refine ⟨i, mem_filter.mpr ⟨by rw [T.descendantLeaves_root]; exact mem_univ _, ?_⟩⟩
      intro w hw hiw
      rcases mem_insert.mp (hB.le hw) with he | hwLeaf
      · rw [he]
      · obtain ⟨j, _, hj⟩ := mem_map.mp hwLeaf
        change j.val = w at hj
        have hij : i = j := mem_singleton.mp (by simpa only [← hj, T.descendantLeaves_leaf j] using hiw)
        have hwv : w = v := hj.symm.trans ((congrArg Subtype.val hij.symm).trans hi)
        exact (hvB (hwv ▸ hw)).elim
    · have huLeaf : u ∈ T.leafNodes := (mem_insert.mp (hB.le hu)).resolve_left hU
      obtain ⟨i, _, rfl⟩ := mem_map.mp huLeaf
      refine ⟨i, mem_filter.mpr ⟨?_, ?_⟩⟩
      · change i ∈ T.descendantLeaves i.val
        rw [T.descendantLeaves_leaf]
        exact mem_singleton_self _
      · intro w _ hiw
        exact ((T.mem_descendantLeaves_iff w i).mp hiw).depth_le

end LovaszTheta.Circulant.RootedTree
