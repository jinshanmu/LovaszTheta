module

public import LovaszTheta.TreeRankPartition

/-!
# Nested and disjoint descendant-leaf supports

With no unary nodes, a proper ancestor has a strictly larger leaf
support. Distinct node rows are therefore nested or disjoint and
differ at some leaf.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

/-- Every child has a sibling because unary nodes are excluded. -/
lemma exists_other_child {T : RootedTree} {u v : T.Node} (hv : v ∈ T.children u) :
    ∃ w ∈ T.children u, w ≠ v := by
  by_contra h
  apply T.noUnary u
  refine ⟨v, (T.mem_children_iff u v).mp hv, ?_⟩
  intro w hw
  by_contra hne
  exact h ⟨w, (T.mem_children_iff u w).mpr hw, hne⟩

/-- A proper ancestor's descendant-leaf support is strictly larger. -/
lemma IsAncestor.descendantLeaves_ssubset {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) (hne : u ≠ v) :
    T.descendantLeaves v ⊂ T.descendantLeaves u := by
  have hSub := h.descendantLeaves_subset
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hSub, ?_⟩
  obtain ⟨w, hw, hwv⟩ := exists_child_ancestor h hne.symm
  obtain ⟨w', hw', hww⟩ := exists_other_child hw
  obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty w'
  have hiu : i ∈ T.descendantLeaves u := by
    have hp : T.IsAncestor u w' := ((T.mem_children_iff u w').mp hw').2 ▸ T.isAncestor_parent w'
    exact hp.descendantLeaves_subset hi
  intro hEq
  have hiv : i ∈ T.descendantLeaves v := hEq.symm ▸ hiu
  exact disjoint_left.mp (children_descendantLeaves_disjoint hw' hw hww) hi
    (hwv.descendantLeaves_subset hiv)

/-- The descendant-leaf supports form a laminar family. -/
lemma descendantLeaves_disjoint_or_nested (T : RootedTree) (u v : T.Node) :
    Disjoint (T.descendantLeaves u) (T.descendantLeaves v) ∨
      T.descendantLeaves u ⊆ T.descendantLeaves v ∨ T.descendantLeaves v ⊆ T.descendantLeaves u := by
  by_cases h : Disjoint (T.descendantLeaves u) (T.descendantLeaves v)
  · exact Or.inl h
  obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp h
  rcases ((T.mem_descendantLeaves_iff u i).mp hi).comparable
    ((T.mem_descendantLeaves_iff v i).mp hi') with h | h
  · exact Or.inr (Or.inr h.descendantLeaves_subset)
  · exact Or.inr (Or.inl h.descendantLeaves_subset)

/-- A descendant-leaf support uniquely specifies its node. -/
theorem descendantLeaves_injective (T : RootedTree) :
    Function.Injective T.descendantLeaves := by
  intro u v he
  obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty u
  have hi' : i ∈ T.descendantLeaves v := he ▸ hi
  by_contra hne
  rcases ((T.mem_descendantLeaves_iff u i).mp hi).comparable
    ((T.mem_descendantLeaves_iff v i).mp hi') with h | h
  · exact (ne_of_lt (h.descendantLeaves_ssubset hne)) he.symm
  · exact (ne_of_lt (h.descendantLeaves_ssubset (Ne.symm hne))) he

end LovaszTheta.Circulant.RootedTree
