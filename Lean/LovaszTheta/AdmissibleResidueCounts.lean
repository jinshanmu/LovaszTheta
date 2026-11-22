module

public import LovaszTheta.SignedNodeMatches

/-!
# Exceptional leaf assignments in the covariance count

Zero and self-opposite residues, and coincidences up to sign, are
controlled by single linear congruences. The coefficient at a
distinguishing leaf has absolute value one for a coincidence.
-/

@[expose] public section

open Finset
open scoped Classical symmDiff

namespace LovaszTheta.Circulant

variable {n : ℕ}

/-- Admissible assignments whose node residues do not use a singleton
inversion class. -/
def RegularAssignment (T : RootedTree) (a : T.Leaf → ZMod n) : Prop :=
  T.Admissible a ∧ ∀ v, T.residue a v + T.residue a v ≠ 0

variable [NeZero n]

private lemma card_filter_le_of_congruence {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (i : I) (hc : c i ≠ 0) (p : (I → ZMod n) → Prop) [DecidablePred p]
    (hp : ∀ a, p a → ∑ j, (c j : ZMod n) * a j = 0) :
    (univ.filter p).card ≤ (c i).natAbs * n^(Fintype.card I-1) := by
  rw [← Fintype.card_subtype p]
  exact (Fintype.card_subtype_mono p (fun a ↦ ∑ j, (c j : ZMod n) * a j = 0) hp).trans
    (card_linear_congruence_fibre_le c i hc 0)

private lemma card_selfOpposite_le (T : RootedTree) (u : T.Node) :
    ((univ : Finset (T.Leaf → ZMod n)).filter
      (fun a ↦ T.residue a u + T.residue a u = 0)).card ≤
      2 * n ^ (Fintype.card T.Leaf - 1) := by
  obtain ⟨i, hi⟩ := T.descendantLeaves_nonempty u
  let c (j : T.Leaf) := T.leafRowInt u j + T.leafRowInt u j
  have hc : c i = 2 := by simp [c, RootedTree.leafRowInt, hi]
  have hSum (a : T.Leaf → ZMod n) :
      (∑ j, (c j : ZMod n) * a j) = T.residue a u + T.residue a u := by
    simp only [c, Int.cast_add, add_mul, sum_add_distrib, T.sum_leafRowInt_mul]
  have h := card_filter_le_of_congruence c i (by rw [hc]; norm_num)
    (fun a ↦ T.residue a u + T.residue a u = 0) (fun a ha ↦ (hSum a).trans ha)
  simpa only [hc, show (2 : ℤ).natAbs = 2 by rfl] using h

private lemma card_coincidence_le (T : RootedTree) {u v : T.Node} (huv : u ≠ v) (o : Bool) :
    ((univ : Finset (T.Leaf → ZMod n)).filter
      (fun a ↦ T.residue a u + (if o then T.residue a v else -T.residue a v) = 0)).card ≤
      n ^ (Fintype.card T.Leaf - 1) := by
  let c (j : T.Leaf) := T.leafRowInt u j + (if o then T.leafRowInt v j else -T.leafRowInt v j)
  have hUnequal : T.descendantLeaves u ≠ T.descendantLeaves v := fun he ↦
    huv (T.descendantLeaves_injective he)
  have h : (T.descendantLeaves u ∆ T.descendantLeaves v).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun he ↦ hUnequal (Finset.symmDiff_eq_empty.mp he)
  obtain ⟨i, hi⟩ := h
  have hCoeff : c i ≠ 0 ∧ (c i).natAbs = 1 := by
    rcases mem_symmDiff.mp hi with ⟨hU, hV⟩ | ⟨hV, hU⟩
    · cases o <;> simp [c, RootedTree.leafRowInt, hU, hV]
    · cases o <;> simp [c, RootedTree.leafRowInt, hU, hV]
  have hSum (a : T.Leaf → ZMod n) :
      (∑ j, (c j : ZMod n) * a j) =
        T.residue a u + (if o then T.residue a v else -T.residue a v) := by
    cases o <;> simp [c, Int.cast_add, Int.cast_neg, add_mul, neg_mul, sum_add_distrib,
      sum_neg_distrib, T.sum_leafRowInt_mul]
  have hBound := card_filter_le_of_congruence c i hCoeff.1
    (fun a ↦ T.residue a u + (if o then T.residue a v else -T.residue a v) = 0)
    (fun a ha ↦ (hSum a).trans ha)
  simpa only [hCoeff.2, one_mul] using hBound

/-- The exceptional choices in the unrestricted leaf sum have one
fewer free residue, uniformly over the modulus. -/
theorem card_not_regularAssignment_le (T : RootedTree) :
    Fintype.card {a : T.Leaf → ZMod n // ¬RegularAssignment T a} ≤
      (2 * T.nodeCount + 2 * T.nodeCount^2) * n ^ (Fintype.card T.Leaf - 1) := by
  let X := T.Leaf → ZMod n
  let Y (u : T.Node) : Finset X :=
    univ.filter fun a ↦ T.residue a u + T.residue a u = 0
  let P := T.Node × T.Node × Bool
  let Z (p : P) : Finset X :=
    if p.1 = p.2.1 then ∅ else univ.filter fun a ↦
      T.residue a p.1 + (if p.2.2 then T.residue a p.2.1 else -T.residue a p.2.1) = 0
  let Yall := (univ : Finset T.Node).biUnion Y
  let Zall := (univ : Finset P).biUnion Z
  have hCover : (univ.filter (fun a : X ↦ ¬RegularAssignment T a)) ⊆ Yall ∪ Zall := by
    intro a ha
    by_contra hnot
    have hOpp (u : T.Node) : T.residue a u + T.residue a u ≠ 0 := by
      intro he
      apply hnot
      exact mem_union_left _ (mem_biUnion.mpr ⟨u, mem_univ _, mem_filter.mpr ⟨mem_univ _, he⟩⟩)
    have hNz (u : T.Node) : T.residue a u ≠ 0 := fun he ↦ hOpp u (by simp [he])
    apply (mem_filter.mp ha).2
    refine ⟨⟨hNz, ?_⟩, hOpp⟩
    intro u v hEq
    by_contra hne
    have hEq' := (inversionClass_eq_iff (hNz u) (hNz v)).mp hEq
    have hBad (o : Bool)
        (hR : T.residue a u + (if o then T.residue a v else -T.residue a v) = 0) : False := by
      apply hnot
      apply mem_union_right
      refine mem_biUnion.mpr ⟨(u, v, o), mem_univ _, ?_⟩
      exact by simp [Z, hne, hR]
    rcases hEq' with he | he
    · exact hBad false (by simp [he])
    · exact hBad true (by simp [he])
  let q := n ^ (Fintype.card T.Leaf - 1)
  have hY : Yall.card ≤ T.nodeCount * (2*q) := by
    calc
      _ ≤ ∑ u, (Y u).card := card_biUnion_le
      _ ≤ ∑ _u : T.Node, 2*q := sum_le_sum fun u _ ↦ card_selfOpposite_le T u
      _ = _ := by simp
  have hZ : Zall.card ≤ (T.nodeCount * (T.nodeCount * 2)) * q := by
    calc
      _ ≤ ∑ p, (Z p).card := card_biUnion_le
      _ ≤ ∑ _p : P, q := by
        apply sum_le_sum
        intro p _
        by_cases he : p.1 = p.2.1
        · simp [Z, he]
        · simpa only [Z, he, ite_false] using card_coincidence_le T he p.2.2
      _ = _ := by simp [P, Fintype.card_prod]
  rw [Fintype.card_subtype]
  calc
    _ ≤ (Yall ∪ Zall).card := card_le_card hCover
    _ ≤ Yall.card + Zall.card := card_union_le _ _
    _ ≤ T.nodeCount * (2*q) + (T.nodeCount * (T.nodeCount * 2)) * q := add_le_add hY hZ
    _ = _ := by dsimp [q]; ring

end LovaszTheta.Circulant
