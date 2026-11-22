module

public import LovaszTheta.PreservedNodeRows
public import LovaszTheta.RootDependenceAntichain

/-!
# Preserving matches of the two root rows

The unique largest minimal dependence identifies the leaves.
Evaluating the root relation at those leaves forces a common
orientation. The remaining row supports then recover ancestry
and the parent map.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

namespace RootedTree

lemma isAncestor_iff_descendantLeaves_subset (T : RootedTree) (u v : T.Node) :
    T.IsAncestor u v ↔ T.descendantLeaves v ⊆ T.descendantLeaves u := by
  refine ⟨IsAncestor.descendantLeaves_subset, ?_⟩
  intro h
  obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty v
  rcases ((T.mem_descendantLeaves_iff u i).mp (h hi)).comparable
    ((T.mem_descendantLeaves_iff v i).mp hi) with hUV | hVU
  · exact hUV
  · by_cases he : v = u
    · exact he.symm ▸ T.isAncestor_refl v
    · exact ((ne_of_lt (hVU.descendantLeaves_ssubset he))
        (Subset.antisymm hVU.descendantLeaves_subset h)).elim

lemma IsAncestor.parent_right {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) (hne : u ≠ v) : T.IsAncestor u (T.parent v) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact (hne hk.symm).elim
  | succ k =>
    rw [Function.iterate_succ_apply] at hk
    exact ⟨k, hk⟩

lemma IsAncestor.antisymm {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) (h' : T.IsAncestor v u) : u = v := by
  by_contra hne
  exact (not_lt_of_ge h'.depth_le) (h.depth_lt hne)

end RootedTree

namespace SignedNodeMatch

variable {T S : RootedTree}

private lemma minimalDependence_map (M : SignedNodeMatch T S) (h : M.PreservesParentSums)
    (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) {A : Finset S.Node}
    (hA : S.IsMinimalDependence A) :
    T.IsMinimalDependence (A.map M.node.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · rw [← M.leafRowRank_map_eq h hL, card_map]
    exact hA.1
  · intro B hB
    let C := B.map M.node.symm.toEmbedding
    have hC : C.map M.node.toEmbedding = B := by simp [C, map_map]
    have hC' : C ⊂ A := by
      rw [← map_ssubset_map (f := M.node.toEmbedding), hC]
      exact hB
    rw [← hC, ← M.leafRowRank_map_eq h hL, card_map]
    exact hA.2 C hC'

private lemma matched_leafNodes (M : SignedNodeMatch T S) (h : M.PreservesParentSums)
    (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) (hT : 1 < T.nodeCount)
    (hRoot : M.node S.root = T.root) :
    S.leafNodes.map M.node.toEmbedding = T.leafNodes := by
  have hNodeCount : S.nodeCount = T.nodeCount := by
    simpa only [Fintype.card_fin] using Fintype.card_congr M.node
  have hS : 1 < S.nodeCount := hNodeCount.symm ▸ hT
  have hMem : T.root ∈ S.rootLeafSet.map M.node.toEmbedding :=
    mem_map.mpr ⟨S.root, mem_insert_self _ _, hRoot⟩
  have hCard : (S.rootLeafSet.map M.node.toEmbedding).card = Fintype.card T.Leaf + 1 := by
    rw [card_map, S.card_rootLeafSet hS, hL]
  have he := T.eq_rootLeafSet_of_card_minimal_root hT hMem
    (M.minimalDependence_map h hL (S.isMinimalDependence_rootLeafSet hS)) hCard
  simp only [RootedTree.rootLeafSet, map_insert, Equiv.toEmbedding_apply, hRoot] at he
  ext v
  by_cases hv : v = T.root
  · subst v
    have hN : T.root ∉ S.leafNodes.map M.node.toEmbedding := by
      intro hv
      obtain ⟨w, hw, hwEq⟩ := mem_map.mp hv
      have hwRoot := M.node.injective (hwEq.trans hRoot.symm)
      exact S.root_not_mem_leafNodes hS (hwRoot ▸ hw)
    exact iff_of_false hN (T.root_not_mem_leafNodes hT)
  · have hV := congrArg (fun s : Finset T.Node ↦ v ∈ s) he
    exact Iff.of_eq (by simpa only [mem_insert, hv, false_or] using hV)

private noncomputable def matchedLeafEquiv (M : SignedNodeMatch T S)
    (h : M.PreservesParentSums) (hL : Fintype.card S.Leaf = Fintype.card T.Leaf)
    (hT : 1 < T.nodeCount) (hRoot : M.node S.root = T.root) : S.Leaf ≃ T.Leaf :=
  M.node.subtypeEquiv fun u ↦ by
    rw [← S.mem_leafNodes_iff, ← T.mem_leafNodes_iff, ← M.matched_leafNodes h hL hT hRoot]
    constructor
    · intro hu
      exact mem_map.mpr ⟨u, hu, rfl⟩
    · intro hu
      obtain ⟨v, hv, he⟩ := mem_map.mp hu
      exact (M.node.injective he) ▸ hv

private lemma realRow_apply_sign (M : SignedNodeMatch T S) (v : S.Node) (i : T.Leaf) :
    M.realRow v i = if i ∈ T.descendantLeaves (M.node v) then sign (M.orient v) else 0 := by
  cases h : M.orient v <;> by_cases hi : i ∈ T.descendantLeaves (M.node v) <;>
    simp [realRow, row, RootedTree.leafRowInt, h, hi]

private lemma sign_injective : Function.Injective sign := by
  intro a b h
  cases a <;> cases b
  · rfl
  · norm_num at h
  · norm_num at h
  · rfl

private lemma sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num

/-- If an identity-preserving signed match takes root to root, it is
a rooted isomorphism with a single orientation on all nodes. -/
theorem rootPreserving_parent_and_orientation (M : SignedNodeMatch T S)
    (h : M.PreservesParentSums) (hL : Fintype.card S.Leaf = Fintype.card T.Leaf)
    (hT : 1 < T.nodeCount) (hRoot : M.node S.root = T.root) :
    (∀ v, M.node (S.parent v) = T.parent (M.node v)) ∧
      ∀ v, M.orient v = M.orient S.root := by
  let L := M.matchedLeafEquiv h hL hT hRoot
  have hAtLeaf (i j : S.Leaf) :
      M.realRow j.val (L i) = if i = j then sign (M.orient j.val) else 0 := by
    have hJ : (L j).val = M.node j.val := rfl
    rw [M.realRow_apply_sign, ← hJ, T.descendantLeaves_leaf (L j)]
    by_cases he : i = j
    · subst i
      simp
    · have hl : L i ∉ ({L j} : Finset T.Leaf) := fun hm ↦ he (L.injective (mem_singleton.mp hm))
      rw [ite_eq_right hl, ite_eq_right he]
  have hEval (v : S.Node) (i : S.Leaf) :
      M.realRow v (L i) = if i ∈ S.descendantLeaves v then sign (M.orient i.val) else 0 := by
    have he := congrFun (M.realRow_eq_sum_leaves h v) (L i)
    rw [Finset.sum_apply] at he
    simpa only [hAtLeaf, Finset.sum_ite_eq] using he
  have hLeafSign (i : S.Leaf) : M.orient i.val = M.orient S.root := by
    apply sign_injective
    have he := hEval S.root i
    rw [M.realRow_apply_sign, hRoot, T.descendantLeaves_root, S.descendantLeaves_root] at he
    simpa using he.symm
  have hSupport (v : S.Node) (i : S.Leaf) :
      i ∈ S.descendantLeaves v ↔ L i ∈ T.descendantLeaves (M.node v) := by
    have he := hEval v i
    rw [M.realRow_apply_sign] at he
    by_cases hv : i ∈ S.descendantLeaves v <;> by_cases hM : L i ∈ T.descendantLeaves (M.node v)
    · exact iff_of_true hv hM
    · have hZ : sign (M.orient i.val) = 0 := by simpa only [hv, hM, ite_true, ite_false] using he.symm
      exact (sign_ne_zero _ hZ).elim
    · have hZ : sign (M.orient v) = 0 := by simpa only [hv, hM, ite_true, ite_false] using he
      exact (sign_ne_zero _ hZ).elim
    · exact iff_of_false hv hM
  have hAnc (u v : S.Node) :
      T.IsAncestor (M.node u) (M.node v) ↔ S.IsAncestor u v := by
    rw [T.isAncestor_iff_descendantLeaves_subset, S.isAncestor_iff_descendantLeaves_subset]
    constructor
    · intro hSub i hi
      exact (hSupport u i).mpr (hSub ((hSupport v i).mp hi))
    · intro hSub j hj
      let i := L.symm j
      have hi : L i = j := L.apply_symm_apply j
      rw [← hi] at hj ⊢
      exact (hSupport u i).mp (hSub ((hSupport v i).mpr hj))
  constructor
  · intro v
    by_cases hv : v = S.root
    · rw [hv, S.parent_root, hRoot, T.parent_root]
    have hParentS : S.parent v ≠ v := fun he ↦
      (ne_of_lt (S.depth_parent_lt v hv)) (congrArg S.depth he)
    have hTarget : M.node v ≠ T.root := fun he ↦ hv (M.node.injective (he.trans hRoot.symm))
    have hParentT : T.parent (M.node v) ≠ M.node v := fun he ↦
      (ne_of_lt (T.depth_parent_lt (M.node v) hTarget)) (congrArg T.depth he)
    let w := M.node.symm (T.parent (M.node v))
    have hw : M.node w = T.parent (M.node v) := M.node.apply_symm_apply _
    have hWne : w ≠ v := fun he ↦ hParentT (hw.symm.trans (congrArg M.node he))
    have hForward : T.IsAncestor (M.node (S.parent v)) (T.parent (M.node v)) :=
      ((hAnc (S.parent v) v).mpr (S.isAncestor_parent v)).parent_right
        (fun he ↦ hParentS (M.node.injective he))
    have hBack : S.IsAncestor w v := (hAnc w v).mp (hw.symm ▸ T.isAncestor_parent (M.node v))
    have hReverse := (hAnc w (S.parent v)).mpr (hBack.parent_right hWne)
    rw [hw] at hReverse
    exact hForward.antisymm hReverse
  · intro v
    obtain ⟨i, hi⟩ := S.descendantLeaves_nonempty v
    have hi' := (hSupport v i).mp hi
    have he := hEval v i
    rw [M.realRow_apply_sign, ite_eq_left hi', ite_eq_left hi, hLeafSign i] at he
    exact sign_injective he

end SignedNodeMatch

end LovaszTheta.Circulant
