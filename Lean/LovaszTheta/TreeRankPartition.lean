module

public import LovaszTheta.TreeRankCounts

/-!
# Rank across a partition of tree nodes

Each parent's leaf row is the sum of its children's rows. A cut of
the parent edges therefore yields a nonzero vector in the
intersection of the two row spans.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

/-- The proper children of a node, excluding the root's parent loop. -/
noncomputable def children (T : RootedTree) (u : T.Node) : Finset T.Node :=
  univ.filter fun v ↦ v ≠ u ∧ T.parent v = u

lemma mem_children_iff (T : RootedTree) (u v : T.Node) :
    v ∈ T.children u ↔ v ≠ u ∧ T.parent v = u := by
  simp [children]

/-- A strict descendant lies below one of the node's immediate children. -/
lemma exists_child_ancestor {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) (hne : v ≠ u) :
    ∃ w ∈ T.children u, T.IsAncestor w v := by
  have hStep := Nat.find_spec h
  have hPos : Nat.find h ≠ 0 := by
    intro he
    rw [he] at hStep
    exact hne hStep
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hPos
  let w := (T.parent^[j]) v
  have hParent : T.parent w = u := by
    rw [hj, Function.iterate_succ_apply'] at hStep
    exact hStep
  have hne' : w ≠ u := fun he ↦ by
    have hmin := Nat.find_min' h he
    omega
  exact ⟨w, (T.mem_children_iff u w).mpr ⟨hne', hParent⟩, ⟨j, rfl⟩⟩

private lemma not_ancestor_of_distinct_children {T : RootedTree} {u v w : T.Node}
    (hv : v ∈ T.children u) (hw : w ∈ T.children u) (hne : v ≠ w) :
    ¬T.IsAncestor v w := by
  obtain ⟨hvNe, hvParent⟩ := (T.mem_children_iff u v).mp hv
  obtain ⟨_, hwParent⟩ := (T.mem_children_iff u w).mp hw
  rintro ⟨j, hj⟩
  cases j with
  | zero => exact hne hj.symm
  | succ j =>
    rw [Function.iterate_succ_apply, hwParent] at hj
    have hAnc : T.IsAncestor v u := ⟨j, hj⟩
    have hvRoot : v ≠ T.root := fun he ↦ hvNe (by simpa only [he, T.parent_root] using hvParent)
    have hDepth := T.depth_parent_lt v hvRoot
    rw [hvParent] at hDepth
    exact (not_lt_of_ge hAnc.depth_le) hDepth

lemma children_descendantLeaves_disjoint {T : RootedTree} {u v w : T.Node}
    (hv : v ∈ T.children u) (hw : w ∈ T.children u) (hne : v ≠ w) :
    Disjoint (T.descendantLeaves v) (T.descendantLeaves w) := by
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  rcases ((T.mem_descendantLeaves_iff v i).mp hi).comparable
    ((T.mem_descendantLeaves_iff w i).mp hi') with h | h
  · exact not_ancestor_of_distinct_children hv hw hne h
  · exact not_ancestor_of_distinct_children hw hv hne.symm h

/-- The children partition the leaves below each internal node. -/
lemma descendantLeaves_eq_children (T : RootedTree) {u : T.Node} (hu : (T.children u).Nonempty) :
    T.descendantLeaves u = (T.children u).biUnion T.descendantLeaves := by
  ext i
  constructor
  · intro hi
    have hne : i.val ≠ u := by
      intro he
      obtain ⟨v, hv⟩ := hu
      obtain ⟨hvu, hParent⟩ := (T.mem_children_iff u v).mp hv
      exact hvu ((i.property v (hParent.trans he.symm)).trans he)
    obtain ⟨v, hv, hvi⟩ := exists_child_ancestor ((T.mem_descendantLeaves_iff u i).mp hi) hne
    exact mem_biUnion.mpr ⟨v, hv, (T.mem_descendantLeaves_iff v i).mpr hvi⟩
  · intro hi
    obtain ⟨v, hv, hvi⟩ := mem_biUnion.mp hi
    have hPar : T.IsAncestor u v := ((T.mem_children_iff u v).mp hv).2 ▸ T.isAncestor_parent v
    exact hPar.descendantLeaves_subset hvi

lemma leafRow_eq_sum_children (T : RootedTree) {u : T.Node} (hu : (T.children u).Nonempty) :
    T.leafRow u = ∑ v ∈ T.children u, T.leafRow v := by
  simp only [leafRow_eq_sum]
  rw [T.descendantLeaves_eq_children hu, sum_biUnion]
  exact fun _ hv _ hw hne ↦ children_descendantLeaves_disjoint hv hw hne

/-- The descendant-leaf rows span all leaf vectors. -/
lemma span_leafRows (T : RootedTree) :
    Submodule.span ℝ (Set.range T.leafRow) = ⊤ := by
  apply top_unique
  intro x _
  rw [pi_eq_sum_univ' x]
  apply Submodule.sum_mem
  intro i _
  have hRow : T.leafRow i.val = (Pi.single i 1 : T.Leaf → ℝ) := by
    rw [leafRow_eq_sum, T.descendantLeaves_leaf, sum_singleton]
  rw [← hRow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- The rank inequality for every nontrivial partition of the nodes. -/
theorem leafRowRank_add_complement_ge (T : RootedTree) (A : Finset T.Node)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    Fintype.card T.Leaf + 1 ≤ leafRowRank T.leafRow A + leafRowRank T.leafRow Aᶜ := by
  apply leafRowRank_add_compl T.leafRow T.root T.parent T.children T.exists_iterate_parent_eq_root
    _ (fun _ ↦ T.leafRow_eq_sum_children) T.span_leafRows _ _ A hA hAc
  · intro v
    by_cases h : T.parent v = v
    · exact Or.inr h
    · exact Or.inl ((T.mem_children_iff (T.parent v) v).mpr ⟨fun he ↦ h he.symm, rfl⟩)
  · intro v i
    unfold leafRow
    split_ifs <;> norm_num
  · intro v
    obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty v
    exact ⟨i, by simp [leafRow, hi]⟩

end LovaszTheta.Circulant.RootedTree
