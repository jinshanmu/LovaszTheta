module

public import LovaszTheta.TreeFields
public import Mathlib.Data.Finset.Max

/-!
# Elimination of selected descendant-leaf rows

For any selection of tree nodes, assign each leaf to its deepest
selected ancestor. The assigned leaf sets are disjoint. Their sums
are obtained from the selected node sums by elimination from the
deepest nodes upward, over any additive commutative group.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

/-- The ancestor relation includes equality. -/
def IsAncestor (T : RootedTree) (u v : T.Node) : Prop :=
  ∃ k : ℕ, (T.parent^[k]) v = u

lemma isAncestor_refl (T : RootedTree) (u : T.Node) : T.IsAncestor u u := ⟨0, rfl⟩

lemma IsAncestor.trans {T : RootedTree} {u v w : T.Node}
    (huv : T.IsAncestor u v) (hvw : T.IsAncestor v w) : T.IsAncestor u w := by
  obtain ⟨j, hj⟩ := huv
  obtain ⟨k, hk⟩ := hvw
  exact ⟨j+k, by rw [Function.iterate_add_apply, hk, hj]⟩

lemma isAncestor_parent (T : RootedTree) (v : T.Node) : T.IsAncestor (T.parent v) v := ⟨1, rfl⟩

private lemma iterate_parent_root (T : RootedTree) (j : ℕ) :
    (T.parent^[j]) T.root = T.root := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, T.parent_root]

private lemma depth_parent_le (T : RootedTree) (v : T.Node) : T.depth (T.parent v) ≤ T.depth v := by
  by_cases hv : v = T.root
  · rw [hv, T.parent_root]
  · exact (T.depth_parent_lt v hv).le

private lemma depth_iterate_le (T : RootedTree) (v : T.Node) (j : ℕ) :
    T.depth ((T.parent^[j]) v) ≤ T.depth v := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (T.depth_parent_le _).trans ih

lemma IsAncestor.depth_le {T : RootedTree} {u v : T.Node} (h : T.IsAncestor u v) :
    T.depth u ≤ T.depth v := by
  obtain ⟨j, rfl⟩ := h
  exact T.depth_iterate_le v j

lemma IsAncestor.depth_lt {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) (hne : u ≠ v) : T.depth u < T.depth v := by
  obtain ⟨j, rfl⟩ := h
  have hv : v ≠ T.root := fun he ↦ hne (by rw [he, T.iterate_parent_root])
  cases j with
  | zero => exact (hne rfl).elim
  | succ j =>
    rw [Function.iterate_succ_apply]
    exact (T.depth_iterate_le (T.parent v) j).trans_lt (T.depth_parent_lt v hv)

/-- Any two ancestors of the same node are comparable. -/
lemma IsAncestor.comparable {T : RootedTree} {u v w : T.Node}
    (hu : T.IsAncestor u w) (hv : T.IsAncestor v w) : T.IsAncestor u v ∨ T.IsAncestor v u := by
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  by_cases h : i ≤ j
  · exact Or.inr ⟨j-i, by rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel h, hj]⟩
  · exact Or.inl ⟨i-j, by
      rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_not_ge h), hi]⟩

lemma mem_descendantLeaves_iff (T : RootedTree) (u : T.Node) (i : T.Leaf) :
    i ∈ T.descendantLeaves u ↔ T.IsAncestor u i.val := by
  simp [descendantLeaves, IsAncestor]

lemma IsAncestor.descendantLeaves_subset {T : RootedTree} {u v : T.Node}
    (h : T.IsAncestor u v) : T.descendantLeaves v ⊆ T.descendantLeaves u := by
  intro i hi
  rw [mem_descendantLeaves_iff] at hi ⊢
  exact h.trans hi

/-- Every node has a descendant leaf, found by maximizing depth. -/
lemma descendantLeaves_nonempty (T : RootedTree) (u : T.Node) : (T.descendantLeaves u).Nonempty := by
  let desc := univ.filter (T.IsAncestor u)
  have hDesc : desc.Nonempty := ⟨u, mem_filter.mpr ⟨mem_univ _, T.isAncestor_refl u⟩⟩
  obtain ⟨v, hv, hMax⟩ := exists_max_image desc T.depth hDesc
  have ha : T.IsAncestor u v := (mem_filter.mp hv).2
  have hLeaf (w : T.Node) (hw : T.parent w = v) : w = v := by
    by_contra hne
    have hwRoot : w ≠ T.root := fun h ↦ hne (by simpa only [h, T.parent_root] using hw)
    have hlt := T.depth_parent_lt w hwRoot
    rw [hw] at hlt
    exact (not_lt_of_ge (hMax w (mem_filter.mpr ⟨mem_univ _, ha.trans (hw ▸ T.isAncestor_parent w)⟩))) hlt
  exact ⟨⟨v, hLeaf⟩, (T.mem_descendantLeaves_iff u _).mpr ha⟩

/-- Leaves in the row of u after removing its proper selected descendants. -/
noncomputable def residualLeaves (T : RootedTree) (A : Finset T.Node) (u : T.Node) :
    Finset T.Leaf :=
  (T.descendantLeaves u).filter fun i ↦
    ∀ v ∈ A, i ∈ T.descendantLeaves v → T.depth v ≤ T.depth u

/-- The nonempty rows after elimination are disjoint. -/
lemma residualLeaves_disjoint (T : RootedTree) (A : Finset T.Node)
    {u v : T.Node} (hu : u ∈ A) (hv : v ∈ A) (h : u ≠ v) :
    Disjoint (T.residualLeaves A u) (T.residualLeaves A v) := by
  apply disjoint_left.mpr
  intro i hi hi'
  obtain ⟨hIu, hMaxu⟩ := mem_filter.mp hi
  obtain ⟨hIv, hMaxv⟩ := mem_filter.mp hi'
  rcases ((T.mem_descendantLeaves_iff u i).mp hIu).comparable
      ((T.mem_descendantLeaves_iff v i).mp hIv) with huv | hvu
  · exact (not_lt_of_ge (hMaxu v hv hIv)) (huv.depth_lt h)
  · exact (not_lt_of_ge (hMaxv u hu hIu)) (hvu.depth_lt h.symm)

private lemma descendantLeaves_eq_biUnion_residual (T : RootedTree) {A : Finset T.Node}
    {u : T.Node} (hu : u ∈ A) :
    T.descendantLeaves u = (A.filter (T.IsAncestor u)).biUnion (T.residualLeaves A) := by
  ext i
  constructor
  · intro hi
    let S := A.filter (fun v ↦ i ∈ T.descendantLeaves v)
    obtain ⟨v, hv, hMax⟩ := exists_max_image S T.depth ⟨u, mem_filter.mpr ⟨hu, hi⟩⟩
    obtain ⟨hvA, hIv⟩ := mem_filter.mp hv
    have huV : T.IsAncestor u v := by
      rcases ((T.mem_descendantLeaves_iff u i).mp hi).comparable
          ((T.mem_descendantLeaves_iff v i).mp hIv) with h | h
      · exact h
      · by_cases he : v = u
        · exact he ▸ T.isAncestor_refl u
        · have hle := hMax u (mem_filter.mpr ⟨hu, hi⟩)
          exact ((not_lt_of_ge hle) (h.depth_lt he)).elim
    exact mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨hvA, huV⟩,
      mem_filter.mpr ⟨hIv, fun w hw hiw ↦ hMax w (mem_filter.mpr ⟨hw, hiw⟩)⟩⟩
  · intro hi
    obtain ⟨v, hv, hIv⟩ := mem_biUnion.mp hi
    exact (mem_filter.mp hv).2.descendantLeaves_subset (mem_filter.mp hIv).1

/-- A selected node sum is the sum of its surviving descendant rows. -/
lemma sum_descendantLeaves_eq_sum_residual {G : Type*} [AddCommMonoid G] (T : RootedTree)
    {A : Finset T.Node} {u : T.Node} (hu : u ∈ A) (x : T.Leaf → G) :
    (∑ i ∈ T.descendantLeaves u, x i) =
      ∑ v ∈ A.filter (T.IsAncestor u), ∑ i ∈ T.residualLeaves A v, x i := by
  rw [T.descendantLeaves_eq_biUnion_residual hu, Finset.sum_biUnion]
  exact fun v hv w hw hne ↦ T.residualLeaves_disjoint A (mem_filter.mp hv).1 (mem_filter.mp hw).1 hne

/-- The surviving sums are determined by the node sums prescribed on A. -/
lemma sum_residualLeaves_congr {G : Type*} [AddCommGroup G] (T : RootedTree)
    (A : Finset T.Node) (x y : T.Leaf → G)
    (h : ∀ v ∈ A, (∑ i ∈ T.descendantLeaves v, x i) = ∑ i ∈ T.descendantLeaves v, y i) :
    ∀ v ∈ A, (∑ i ∈ T.residualLeaves A v, x i) = ∑ i ∈ T.residualLeaves A v, y i := by
  let depthMax := (univ : Finset T.Node).sup T.depth
  have hMax (v : T.Node) : T.depth v ≤ depthMax := le_sup (mem_univ v)
  intro v
  induction hm : depthMax - T.depth v using Nat.strong_induction_on generalizing v with
  | ind m ih =>
    intro hv
    let S := A.filter (T.IsAncestor v)
    have hvS : v ∈ S := mem_filter.mpr ⟨hv, T.isAncestor_refl v⟩
    have hSum :
        (∑ w ∈ S, ∑ i ∈ T.residualLeaves A w, x i) =
          ∑ w ∈ S, ∑ i ∈ T.residualLeaves A w, y i :=
      (T.sum_descendantLeaves_eq_sum_residual hv x).symm.trans
        ((h v hv).trans (T.sum_descendantLeaves_eq_sum_residual hv y))
    have hErase : (∑ w ∈ S.erase v, ∑ i ∈ T.residualLeaves A w, x i) =
        ∑ w ∈ S.erase v, ∑ i ∈ T.residualLeaves A w, y i := by
      apply sum_congr rfl
      intro w hw
      obtain ⟨hne, hw⟩ := mem_erase.mp hw
      obtain ⟨hwA, hvw⟩ := mem_filter.mp hw
      have hlt := hvw.depth_lt hne.symm
      exact ih _ (by have := hMax w; omega) w rfl hwA
    rw [← sum_erase_add _ _ hvS, ← sum_erase_add _ _ hvS, hErase] at hSum
    exact add_left_cancel hSum

end LovaszTheta.Circulant.RootedTree
