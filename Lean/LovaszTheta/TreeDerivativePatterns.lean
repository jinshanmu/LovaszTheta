module

public import LovaszTheta.TreeDerivativeTerms

/-!
# Sum over the overlap patterns of a derivative pairing

Use the fixed-pattern second moment on the side with an unmatched
role. The number of overlap codes controls the sum of these moments.
-/

@[expose] public section

open Finset
open scoped Classical symmDiff

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private lemma sharedRoles_nonempty_iff (T S : RootedTree) (a : T.Assignment n) (b : S.Assignment n) :
    (sharedRoles (overlapCode T S a b)).Nonempty ↔ (T.signSupport a ∩ S.signSupport b).Nonempty := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨T.classEmbedding a u, mem_inter.mpr
      ⟨mem_map.mpr ⟨u, mem_univ _, rfl⟩, (sharedRoles_mem_iff a b u).mp hu⟩⟩
  · rintro ⟨c, hc⟩
    obtain ⟨u, _, hu⟩ := mem_map.mp (mem_inter.mp hc).1
    exact ⟨u, (sharedRoles_mem_iff a b u).mpr (hu ▸ (mem_inter.mp hc).2)⟩

omit [NeZero n] in
private lemma unsharedRoles_nonempty_iff (T S : RootedTree) (a : T.Assignment n) (b : S.Assignment n) :
    (sharedRoles (overlapCode T S a b))ᶜ.Nonempty ↔ ¬T.signSupport a ⊆ S.signSupport b := by
  rw [not_subset]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨T.classEmbedding a u, mem_map.mpr ⟨u, mem_univ _, rfl⟩,
      fun hm ↦ mem_compl.mp hu ((sharedRoles_mem_iff a b u).mpr hm)⟩
  · rintro ⟨c, hc, hnc⟩
    obtain ⟨u, _, hu⟩ := mem_map.mp hc
    exact ⟨u, mem_compl.mpr fun h ↦ hnc (hu ▸ (sharedRoles_mem_iff a b u).mp h)⟩

/-- The part of the derivative sum on which the first tree has an unmatched
role, with an optional restriction on the assignment pairs. -/
noncomputable def unmatchedDerivativeSum (T S : RootedTree) (k j : ZMod n)
    (keep : T.Assignment n × S.Assignment n → Prop) (x : InversionClass n → Bool) : ℝ :=
  ∑ ab : T.Assignment n × S.Assignment n,
    if (¬T.signSupport ab.1 ⊆ S.signSupport ab.2) ∧ keep ab then
      derivativePairWeight T S k j ab.1 ab.2 * walsh (assignmentDifference T S ab.1 ab.2) x
    else 0

private noncomputable def derivativePatternSum (T S : RootedTree) (k j : ZMod n)
    (keep : T.Assignment n × S.Assignment n → Prop) (c : OverlapCode T S)
    (x : InversionClass n → Bool) : ℝ :=
  if (sharedRoles c).Nonempty ∧ (sharedRoles c)ᶜ.Nonempty then
    ∑ ab : {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c},
      (if keep ab.val then derivativePairWeight T S k j ab.val.1 ab.val.2 else 0) *
        walsh (assignmentDifference T S ab.val.1 ab.val.2) x
  else 0

private lemma unmatchedDerivativeSum_eq_sum_patterns (T S : RootedTree) (k j : ZMod n)
    (keep : T.Assignment n × S.Assignment n → Prop) (x : InversionClass n → Bool) :
    unmatchedDerivativeSum T S k j keep x = ∑ c, derivativePatternSum T S k j keep c x := by
  let f (ab : T.Assignment n × S.Assignment n) : ℝ :=
    if (¬T.signSupport ab.1 ⊆ S.signSupport ab.2) ∧ keep ab then
      derivativePairWeight T S k j ab.1 ab.2 * walsh (assignmentDifference T S ab.1 ab.2) x
    else 0
  have hGroup (c : OverlapCode T S) :
      derivativePatternSum T S k j keep c x =
        ∑ ab : {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c}, f ab.val := by
    unfold derivativePatternSum
    by_cases h : (sharedRoles c).Nonempty ∧ (sharedRoles c)ᶜ.Nonempty
    · rw [ite_eq_left h]
      apply sum_congr rfl
      intro ab _
      have hMismatch : ¬T.signSupport ab.val.1 ⊆ S.signSupport ab.val.2 :=
        (unsharedRoles_nonempty_iff T S ab.val.1 ab.val.2).mp (ab.property.symm ▸ h.2)
      by_cases hk : keep ab.val <;> simp [f, hMismatch, hk]
    · rw [ite_eq_right h]
      symm
      apply sum_eq_zero
      intro ab _
      by_cases hSub : T.signSupport ab.val.1 ⊆ S.signSupport ab.val.2
      · simp [f, hSub]
      have hUnshared := (unsharedRoles_nonempty_iff T S ab.val.1 ab.val.2).mpr hSub
      have hEmpty : ¬(T.signSupport ab.val.1 ∩ S.signSupport ab.val.2).Nonempty := by
        intro he
        have hShared := (sharedRoles_nonempty_iff T S ab.val.1 ab.val.2).mpr he
        exact h ⟨ab.property ▸ hShared, ab.property ▸ hUnshared⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
      simp [f, derivativePairWeight, hEmpty]
  change (∑ ab, f ab) = _
  simp_rw [hGroup]
  let idx (ab : T.Assignment n × S.Assignment n) := overlapCode T S ab.1 ab.2
  let g (ab : Σ c : OverlapCode T S, {ab : T.Assignment n × S.Assignment n // idx ab = c}) :=
    f ab.2.val
  exact (Fintype.sum_equiv (Equiv.sigmaFiberEquiv idx) g f (fun _ ↦ rfl)).symm.trans
    (Fintype.sum_sigma g)

/-- The constant in the moment bound for the side with a proper overlap. -/
noncomputable def unmatchedDerivativeConstant (T S : RootedTree) : ℝ :=
  (T.nodeCount : ℝ) ^ 2 * ((1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) : ℕ) *
    ((1 + 2 * S.nodeCount) ^ T.nodeCount : ℕ) ^ 2

private lemma average_derivativePatternSum_sq_le (T S : RootedTree) (k j : ZMod n)
    (keep : T.Assignment n × S.Assignment n → Prop) (c : OverlapCode T S) :
    average (fun x ↦ derivativePatternSum T S k j keep c x ^ 2) ≤
      (T.nodeCount : ℝ) ^ 2 *
        ((1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) : ℕ) / n := by
  let C := ((1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) : ℕ)
  let l := Fintype.card T.Leaf
  let l' := Fintype.card S.Leaf
  let N := (n : ℝ)
  let t := T.fieldNormalizer n
  let s := S.fieldNormalizer n
  let W := (T.nodeCount : ℝ) * (t * s)
  let w (ab : T.Assignment n × S.Assignment n) :=
    if keep ab then derivativePairWeight T S k j ab.1 ab.2 else 0
  have hN : 0 < N := by
    change (0 : ℝ) < n
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have ht : 0 ≤ t := by unfold t RootedTree.fieldNormalizer; positivity
  have hs : 0 ≤ s := by unfold s RootedTree.fieldNormalizer; positivity
  have hW : 0 ≤ W := by unfold W; positivity
  by_cases h : (sharedRoles c).Nonempty ∧ (sharedRoles c)ᶜ.Nonempty
  · simp only [derivativePatternSum, h]
    have hw (ab : T.Assignment n × S.Assignment n) : |w ab| ≤ W := by
      by_cases hk : keep ab
      · simpa only [w, hk, ite_true] using abs_derivativePairWeight_le T S k j ab.1 ab.2
      · simpa only [w, hk, ite_false, abs_zero] using hW
    have hB := average_overlap_sum_sq_le T S c h.1 h.2 w hW hw
    apply hB.trans
    change W ^ 2 * (C : ℝ) * N ^ (l+l'-1) ≤ (T.nodeCount : ℝ)^2 * C / N
    apply (le_div_iff₀ hN).mpr
    have hl : 0 < l := by
      obtain ⟨i, _⟩ := T.descendantLeaves_nonempty T.root
      let : Nonempty T.Leaf := ⟨i⟩
      exact Fintype.card_pos
    have hPow : N ^ (l+l'-1) * N = N^l * N^l' := by
      rw [← pow_succ, show l+l'-1+1 = l+l' by omega, pow_add]
    have hProd : (t^2 * N^l) * (s^2 * N^l') ≤ 1 := by
      simpa only [one_mul] using
        mul_le_mul (T.fieldNormalizer_sq_mul (n := n)) (S.fieldNormalizer_sq_mul (n := n))
          (by positivity) zero_le_one
    calc
      _ = ((T.nodeCount : ℝ)^2 * C) * (t^2 * s^2 * (N ^ (l+l'-1) * N)) := by dsimp only [W]; ring
      _ = ((T.nodeCount : ℝ)^2 * C) * ((t^2 * N^l) * (s^2 * N^l')) := by rw [hPow]; ring
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hProd (show 0 ≤ ((T.nodeCount : ℝ)^2 * C) by positivity)
  · simp [derivativePatternSum, h]
    positivity

/-- The part of the centered pairing with an unmatched first-tree role has
second moment bounded by its overlap-count constant divided by n. -/
theorem average_unmatchedDerivativeSum_sq_le (T S : RootedTree) (k j : ZMod n)
    (keep : T.Assignment n × S.Assignment n → Prop) :
    average (fun x ↦ unmatchedDerivativeSum T S k j keep x ^ 2) ≤
      unmatchedDerivativeConstant T S / n := by
  simp_rw [unmatchedDerivativeSum_eq_sum_patterns]
  let B := (T.nodeCount : ℝ)^2 * ((1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) : ℕ)
  have hCard : Fintype.card (OverlapCode T S) = (1 + 2*S.nodeCount)^T.nodeCount := by
    simp [OverlapCode, Fintype.card_option, Fintype.card_prod, mul_comm, add_comm]
  calc
    _ ≤ (Fintype.card (OverlapCode T S) : ℝ) *
        ∑ c, average (fun x ↦ derivativePatternSum T S k j keep c x ^ 2) :=
      average_sum_sq_le_card_mul_sum (derivativePatternSum T S k j keep)
    _ ≤ (Fintype.card (OverlapCode T S) : ℝ) * ∑ _c : OverlapCode T S, B / n := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun c _ ↦
        average_derivativePatternSum_sq_le T S k j keep c) (by positivity)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, hCard, unmatchedDerivativeConstant, B]; ring

end LovaszTheta.Circulant
