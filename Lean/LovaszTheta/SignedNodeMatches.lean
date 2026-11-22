module

public import LovaszTheta.DescendantSupport
public import LovaszTheta.LinearCongruences

/-!
# Signed node permutations and parent-sum relations

A signed match of node residues must respect each target parent sum.
A match that fails an integer row identity therefore imposes a
nonzero congruence on the source leaves.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- A target-to-source node permutation with one relative orientation
per target node. -/
structure SignedNodeMatch (T S : RootedTree) where
  /-- The permutation of node roles. -/
  node : S.Node ≃ T.Node
  /-- True denotes the positive orientation. -/
  orient : S.Node → Bool

namespace RootedTree

/-- The integer indicator row of the leaves below a node. -/
noncomputable def leafRowInt (T : RootedTree) (u : T.Node) (i : T.Leaf) : ℤ :=
  if i ∈ T.descendantLeaves u then 1 else 0

lemma residue_eq_sum_children (T : RootedTree) {n : ℕ} (a : T.Leaf → ZMod n) {u : T.Node}
    (hu : (T.children u).Nonempty) :
    T.residue a u = ∑ v ∈ T.children u, T.residue a v := by
  unfold residue
  rw [T.descendantLeaves_eq_children hu, sum_biUnion]
  exact fun _ hv _ hw hne ↦ children_descendantLeaves_disjoint hv hw hne

lemma sum_leafRowInt_mul {n : ℕ} (T : RootedTree) (u : T.Node) (a : T.Leaf → ZMod n) :
    (∑ i, (T.leafRowInt u i : ZMod n) * a i) = T.residue a u := by
  simp only [leafRowInt, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, residue]

end RootedTree

namespace SignedNodeMatch

variable {T S : RootedTree}

/-- The signed source row attached to a target node. -/
noncomputable def row (M : SignedNodeMatch T S) (v : S.Node) (i : T.Leaf) : ℤ :=
  if M.orient v then T.leafRowInt (M.node v) i else -T.leafRowInt (M.node v) i

/-- The difference between the matched parent row and matched child rows. -/
noncomputable def parentRelation (M : SignedNodeMatch T S) (v : S.Node) (i : T.Leaf) : ℤ :=
  M.row v i - ∑ w ∈ S.children v, M.row w i

/-- Every target parent-sum relation is an identity of integer source rows. -/
def PreservesParentSums (M : SignedNodeMatch T S) : Prop :=
  ∀ v, (S.children v).Nonempty → ∀ i, M.parentRelation v i = 0

/-- The source residue with the prescribed orientation at a target node. -/
noncomputable def value {n : ℕ} (M : SignedNodeMatch T S)
    (a : T.Leaf → ZMod n) (v : S.Node) : ZMod n :=
  if M.orient v then T.residue a (M.node v) else -T.residue a (M.node v)

/-- The residue equations imposed by the signed match. -/
def Matches {n : ℕ} (M : SignedNodeMatch T S)
    (a : T.Leaf → ZMod n) (b : S.Leaf → ZMod n) : Prop :=
  ∀ v, S.residue b v = M.value a v

lemma sum_row_mul {n : ℕ} (M : SignedNodeMatch T S) (v : S.Node) (a : T.Leaf → ZMod n) :
    (∑ i, (M.row v i : ZMod n) * a i) = M.value a v := by
  by_cases h : M.orient v
  · simp [row, value, h, T.sum_leafRowInt_mul]
  · simp only [row, value, h, Bool.false_eq_true, ite_false, Int.cast_neg, neg_mul, sum_neg_distrib,
      T.sum_leafRowInt_mul]

lemma sum_parentRelation_mul {n : ℕ} (M : SignedNodeMatch T S) (v : S.Node)
    (a : T.Leaf → ZMod n) :
    (∑ i, (M.parentRelation v i : ZMod n) * a i) =
      M.value a v - ∑ w ∈ S.children v, M.value a w := by
  simp only [parentRelation, Int.cast_sub, Int.cast_sum, sub_mul, sum_sub_distrib, sum_mul]
  rw [sum_comm (s := univ) (t := S.children v)]
  simp_rw [sum_row_mul]

private lemma natAbs_parentRelation_le (M : SignedNodeMatch T S) (v : S.Node) (i : T.Leaf) :
    (M.parentRelation v i).natAbs ≤ S.nodeCount + 1 := by
  have hOne (w : S.Node) : (M.row w i).natAbs ≤ 1 := by
    unfold row RootedTree.leafRowInt
    split_ifs <;> norm_num
  have hSum (A : Finset S.Node) : (∑ w ∈ A, M.row w i).natAbs ≤ A.card := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert w A hw ih =>
      rw [sum_insert hw, card_insert_of_notMem hw]
      exact (Int.natAbs_add_le _ _).trans (by have := hOne w; omega)
  have hCard : (S.children v).card ≤ S.nodeCount := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (S.children v)
  exact (Int.natAbs_sub_le _ _).trans (by
    have hV := hOne v
    have hS := hSum (S.children v)
    omega)

/-- The signed match and source assignment determine the target leaves. -/
lemma target_eq_of_matches {n : ℕ} (M : SignedNodeMatch T S)
    {a : T.Leaf → ZMod n} {b b' : S.Leaf → ZMod n}
    (hb : M.Matches a b) (hb' : M.Matches a b') : b = b' := by
  funext i
  rw [← S.residue_leaf b i, ← S.residue_leaf b' i, hb i.val, hb' i.val]

/-- For a signed node permutation that violates a parent identity, the
number of matching residue assignments loses one power of the modulus. -/
theorem card_matches_le_of_not_preserves {n : ℕ} [NeZero n] (M : SignedNodeMatch T S)
    (h : ¬ M.PreservesParentSums) :
    Fintype.card {ab : (T.Leaf → ZMod n) × (S.Leaf → ZMod n) // M.Matches ab.1 ab.2} ≤
      (S.nodeCount + 1) * n ^ (Fintype.card T.Leaf - 1) := by
  unfold PreservesParentSums at h
  push Not at h
  obtain ⟨v, hv, i, hi⟩ := h
  let X := {ab : (T.Leaf → ZMod n) × (S.Leaf → ZMod n) // M.Matches ab.1 ab.2}
  let a := M.parentRelation v
  let Y := {z : T.Leaf → ZMod n // ∑ i, (a i : ZMod n) * z i = 0}
  have hConstraint (ab : X) :
      (∑ i, (a i : ZMod n) * ab.val.1 i) = 0 := by
    change (∑ i, (M.parentRelation v i : ZMod n) * ab.val.1 i) = 0
    rw [M.sum_parentRelation_mul]
    have hm (w : S.Node) : S.residue ab.val.2 w = M.value ab.val.1 w := ab.property w
    simp_rw [← hm, ← S.residue_eq_sum_children ab.val.2 hv, sub_self]
  let encode (ab : X) : Y := ⟨ab.val.1, hConstraint ab⟩
  have hInj : Function.Injective encode := by
    intro x y he
    have hx : x.val.1 = y.val.1 := congrArg (fun z : Y ↦ z.val) he
    exact Subtype.ext (Prod.ext hx (M.target_eq_of_matches x.property (hx.symm ▸ y.property)))
  calc
    Fintype.card X ≤ Fintype.card Y := Fintype.card_le_of_injective encode hInj
    _ ≤ (a i).natAbs * n ^ (Fintype.card T.Leaf - 1) :=
      card_linear_congruence_fibre_le a i hi 0
    _ ≤ _ := Nat.mul_le_mul_right _ (M.natAbs_parentRelation_le v i)

end SignedNodeMatch

end LovaszTheta.Circulant
