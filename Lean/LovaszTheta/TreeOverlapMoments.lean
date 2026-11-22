module

public import LovaszTheta.TreeOverlapFibres
public import LovaszTheta.WalshMultiplicity

/-!
# The second moment for a fixed tree-overlap pattern

Multiply the total pair count and the largest symmetric-difference
fiber. The rank inequality removes one free residue in the resulting
second moment.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma rank_le_leafCount (T : RootedTree) (A : Finset T.Node) :
    leafRowRank T.leafRow A ≤ Fintype.card T.Leaf := by
  unfold leafRowRank
  rw [← Module.finrank_fintype_fun_eq_card ℝ]
  exact Submodule.finrank_le _

/-- A nontrivial overlap pattern loses one free residue in the
second moment, uniformly over all frequencies and coefficient choices. -/
theorem average_overlap_sum_sq_le (T S : RootedTree) (c : OverlapCode T S)
    (hShared : (sharedRoles c).Nonempty) (hUnshared : (sharedRoles c)ᶜ.Nonempty)
    (w : T.Assignment n × S.Assignment n → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ a, |w a| ≤ W) :
    average (fun x : InversionClass n → Bool ↦
      (∑ ab : {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c},
        w ab.val * walsh (assignmentDifference T S ab.val.1 ab.val.2) x) ^ 2) ≤
      W ^ 2 * ((1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) : ℕ) *
        (n : ℝ) ^ (Fintype.card T.Leaf + Fintype.card S.Leaf - 1) := by
  let X := {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c}
  let A := sharedRoles c
  let d := T.nodeCount + S.nodeCount
  let K : ℕ := (1 + 2*d)^d
  let l := Fintype.card T.Leaf
  let l' := Fintype.card S.Leaf
  let p := l - leafRowRank T.leafRow A
  let q := l - leafRowRank T.leafRow Aᶜ
  let diff (ab : X) := assignmentDifference T S ab.val.1 ab.val.2
  have hFibres (I : Finset (InversionClass n)) :
      (univ.filter fun ab : X ↦ diff ab = I).card ≤ K * n ^ q := by
    let F := univ.filter fun ab : X ↦ diff ab = I
    let Y := {ab : T.Assignment n × S.Assignment n //
      overlapCode T S ab.1 ab.2 = c ∧ assignmentDifference T S ab.1 ab.2 = I}
    let map (ab : F) : Y := ⟨ab.val.val, ab.val.property, (mem_filter.mp ab.property).2⟩
    have hInj : Function.Injective map := fun _ _ he ↦
      Subtype.ext (Subtype.ext (congrArg (fun z : Y ↦ z.val) he))
    change F.card ≤ _
    rw [← Fintype.card_coe]
    exact (Fintype.card_le_of_injective map hInj).trans (card_overlap_difference_pairs_le T S c I)
  have hp : leafRowRank T.leafRow A ≤ l := rank_le_leafCount T A
  have hq : leafRowRank T.leafRow Aᶜ ≤ l := rank_le_leafCount T Aᶜ
  have hRank := T.leafRowRank_add_complement_ge A hShared hUnshared
  have hExp : l' + (p+q) ≤ l+l'-1 := by
    change l' + ((l - leafRowRank T.leafRow A) + (l - leafRowRank T.leafRow Aᶜ)) ≤ _
    change l + 1 ≤ leafRowRank T.leafRow A + leafRowRank T.leafRow Aᶜ at hRank
    omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hCardN : Fintype.card X ≤ n ^ l' * n ^ p := card_overlap_pairs_le T S c
  have hCard : (Fintype.card X : ℝ) ≤ (n : ℝ) ^ l' * (n : ℝ) ^ p := by exact_mod_cast hCardN
  calc
    _ ≤ W ^ 2 * ↑(K * n^q) * Fintype.card X :=
      average_walsh_sum_sq_le_of_multiplicity diff (fun ab ↦ w ab.val) hW
        (fun ab ↦ hw ab.val) _ hFibres
    _ ≤ W ^ 2 * ↑(K * n^q) * ((n : ℝ) ^ l' * (n : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left hCard (by positivity)
    _ = W ^ 2 * K * (n : ℝ) ^ (l' + (p+q)) := by push_cast; rw [pow_add, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hExp) (by positivity)

end LovaszTheta.Circulant
