module

public import LovaszTheta.RootLeafDependence

/-!
# The largest minimal dependence containing the root

The other nodes in a minimal dependence containing the root have
disjoint leaf supports that cover all leaves. The number of these
nodes reaches the number of leaves only for singleton supports.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

private lemma residual_root_empty (T : RootedTree) (A : Finset T.Node)
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) :
    T.residualLeaves A T.root = ∅ := by
  obtain ⟨u, hu, he⟩ := (T.leafRowRank_lt_card_iff_residual_empty A).mp hMin.1
  by_cases h : u = T.root
  · simpa only [h] using he
  let B := A.filter (T.IsAncestor u)
  have huB : u ∈ B := mem_filter.mpr ⟨hu, T.isAncestor_refl u⟩
  have hNotRoot : T.root ∉ B := by
    intro hB
    have hA := (mem_filter.mp hB).2
    have hRootU : T.IsAncestor T.root u := T.exists_iterate_parent_eq_root u
    exact (not_lt_of_ge hRootU.depth_le) (hA.depth_lt h)
  have hProper : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr
    ⟨filter_subset _ _, fun he ↦ hNotRoot (he.symm ▸ hRoot)⟩
  have hEmpty : T.residualLeaves B u = ∅ := by
    apply (T.residualLeaves_eq_empty_iff _ _).mpr
    intro i hi
    obtain ⟨w, hw, hiw, hDepth⟩ := (T.residualLeaves_eq_empty_iff A u).mp he i hi
    have hAnc : T.IsAncestor u w := by
      rcases ((T.mem_descendantLeaves_iff u i).mp hi).comparable
        ((T.mem_descendantLeaves_iff w i).mp hiw) with hUW | hWU
      · exact hUW
      · exact ((not_lt_of_ge hWU.depth_le) hDepth).elim
    exact ⟨w, mem_filter.mpr ⟨hw, hAnc⟩, hiw, hDepth⟩
  have hLt := (T.leafRowRank_lt_card_iff_residual_empty B).mpr ⟨u, huB, hEmpty⟩
  rw [hMin.2 B hProper] at hLt
  exact ((lt_irrefl _) hLt).elim

private lemma rootErase_covers (T : RootedTree) (A : Finset T.Node)
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) :
    (A.erase T.root).biUnion T.descendantLeaves = univ := by
  apply eq_univ_of_forall
  intro i
  have hI : i ∈ T.descendantLeaves T.root := by rw [T.descendantLeaves_root]; exact mem_univ _
  obtain ⟨w, hw, hiw, hLt⟩ := (T.residualLeaves_eq_empty_iff A T.root).mp
    (T.residual_root_empty A hRoot hMin) i hI
  have hNe : w ≠ T.root := fun he ↦ (Nat.lt_irrefl _) (he ▸ hLt)
  exact mem_biUnion.mpr ⟨w, mem_erase.mpr ⟨hNe, hw⟩, hiw⟩

private lemma not_ancestor_of_minimal_root (T : RootedTree) {A : Finset T.Node}
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) {u v : T.Node}
    (hu : u ∈ A.erase T.root) (hv : v ∈ A.erase T.root) (hne : u ≠ v) :
    ¬T.IsAncestor u v := by
  intro hAnc
  obtain ⟨huNe, huA⟩ := mem_erase.mp hu
  obtain ⟨hvNe, hvA⟩ := mem_erase.mp hv
  let B := A.erase v
  have hRB : T.root ∈ B := mem_erase.mpr ⟨hvNe.symm, hRoot⟩
  have hE : T.residualLeaves B T.root = ∅ := by
    apply (T.residualLeaves_eq_empty_iff _ _).mpr
    intro i hi
    obtain ⟨w, hw, hiw, hDepth⟩ := (T.residualLeaves_eq_empty_iff A T.root).mp
      (T.residual_root_empty A hRoot hMin) i hi
    by_cases hEq : w = v
    · subst w
      have hAncRoot : T.IsAncestor T.root u := T.exists_iterate_parent_eq_root u
      exact ⟨u, mem_erase.mpr ⟨hne, huA⟩, hAnc.descendantLeaves_subset hiw,
        hAncRoot.depth_lt huNe.symm⟩
    · exact ⟨w, mem_erase.mpr ⟨hEq, hw⟩, hiw, hDepth⟩
  have hLt := (T.leafRowRank_lt_card_iff_residual_empty B).mpr ⟨T.root, hRB, hE⟩
  rw [hMin.2 B (erase_ssubset hvA)] at hLt
  exact (lt_irrefl _) hLt

private lemma rootErase_pairwiseDisjoint (T : RootedTree) {A : Finset T.Node}
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) :
    (↑(A.erase T.root) : Set T.Node).PairwiseDisjoint T.descendantLeaves := by
  intro u hu v hv hne
  by_contra hD
  obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp hD
  rcases ((T.mem_descendantLeaves_iff u i).mp hi).comparable
    ((T.mem_descendantLeaves_iff v i).mp hi') with h | h
  · exact T.not_ancestor_of_minimal_root hRoot hMin hu hv hne h
  · exact T.not_ancestor_of_minimal_root hRoot hMin hv hu hne.symm h

private lemma sum_card_rootErase (T : RootedTree) (A : Finset T.Node)
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) :
    (∑ v ∈ A.erase T.root, (T.descendantLeaves v).card) = Fintype.card T.Leaf := by
  rw [← card_biUnion (T.rootErase_pairwiseDisjoint hRoot hMin), T.rootErase_covers A hRoot hMin,
    card_univ]

lemma mem_leafNodes_of_descendantLeaves_card_one (T : RootedTree) (u : T.Node)
    (h : (T.descendantLeaves u).card = 1) : u ∈ T.leafNodes := by
  apply (T.mem_leafNodes_iff u).mpr
  intro v hv
  by_contra hne
  have hvC : v ∈ T.children u := (T.mem_children_iff u v).mpr ⟨hne, hv⟩
  obtain ⟨w, hw, hwv⟩ := exists_other_child hvC
  obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty v
  obtain ⟨j, hj⟩ := T.descendantLeaves_nonempty w
  have hDiff : i ≠ j := fun he ↦ disjoint_left.mp (children_descendantLeaves_disjoint hw hvC hwv) hj
    (he ▸ hi)
  have hvA : T.IsAncestor u v := hv ▸ T.isAncestor_parent v
  have hwA : T.IsAncestor u w := ((T.mem_children_iff u w).mp hw).2 ▸ T.isAncestor_parent w
  have hCard := Finset.one_lt_card.mpr ⟨i, hvA.descendantLeaves_subset hi,
    j, hwA.descendantLeaves_subset hj, hDiff⟩
  omega

private lemma card_le_sum_descendantLeaves_card (T : RootedTree) (B : Finset T.Node) :
    B.card ≤ ∑ v ∈ B, (T.descendantLeaves v).card := by
  calc
    _ = ∑ _v ∈ B, (1 : ℕ) := by simp
    _ ≤ _ := sum_le_sum fun v _ ↦ card_pos.mpr (T.descendantLeaves_nonempty v)

/-- A minimal dependence containing the root has at most one member
per leaf in addition to the root. -/
theorem card_minimal_root_le (T : RootedTree) {A : Finset T.Node}
    (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A) :
    A.card ≤ Fintype.card T.Leaf + 1 := by
  have hCard : (A.erase T.root).card ≤ Fintype.card T.Leaf := by
    rw [← T.sum_card_rootErase A hRoot hMin]
    exact T.card_le_sum_descendantLeaves_card _
  rw [card_erase_of_mem hRoot] at hCard
  omega

/-- Among the root-containing minimal dependencies, the root and all
leaves are the unique set of maximal size. -/
theorem eq_rootLeafSet_of_card_minimal_root (T : RootedTree) (hT : 1 < T.nodeCount)
    {A : Finset T.Node} (hRoot : T.root ∈ A) (hMin : T.IsMinimalDependence A)
    (hCard : A.card = Fintype.card T.Leaf + 1) : A = T.rootLeafSet := by
  apply Finset.eq_of_subset_of_card_le _ ((T.card_rootLeafSet hT).trans hCard.symm).le
  intro u hu
  by_cases he : u = T.root
  · subst u
    exact mem_insert_self _ _
  have huB : u ∈ A.erase T.root := mem_erase.mpr ⟨he, hu⟩
  have hRest : ((A.erase T.root).erase u).card ≤
      ∑ v ∈ (A.erase T.root).erase u, (T.descendantLeaves v).card := by
    exact T.card_le_sum_descendantLeaves_card _
  have hTot := T.sum_card_rootErase A hRoot hMin
  rw [← sum_erase_add _ _ huB] at hTot
  rw [card_erase_of_mem huB, card_erase_of_mem hRoot, hCard] at hRest
  have hPositive := card_pos.mpr (T.descendantLeaves_nonempty u)
  exact mem_insert_of_mem (T.mem_leafNodes_of_descendantLeaves_card_one u (by omega))

end LovaszTheta.Circulant.RootedTree
