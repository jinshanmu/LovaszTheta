module

public import LovaszTheta.TreeDerivativePatterns

/-!
# The derivative variance of two tree fields

Centering removes the pairs with equal supports. For each remaining
pair, choose a tree with an unmatched role and apply the corresponding
pattern bound.
-/

@[expose] public section

open Finset
open scoped Classical symmDiff

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The derivative pairing in the Gaussian comparison, normalized by the
degree of the first tree coordinate. -/
noncomputable def normalizedTreeDerivativePairing (T S : RootedTree) (k j : ZMod n)
    (x : InversionClass n → Bool) : ℝ :=
  (∑ b, walshPartial (T.fieldCoefficient k) b x * walshPartial (S.fieldCoefficient j) b x) / T.nodeCount

private lemma centered_treePartials_eq (T S : RootedTree) (k j : ZMod n) (x : InversionClass n → Bool) :
    let Q (y : InversionClass n → Bool) :=
      ∑ b, walshPartial (T.fieldCoefficient k) b y * walshPartial (S.fieldCoefficient j) b y
    Q x - average Q =
      unmatchedDerivativeSum T S k j (fun _ ↦ True) x +
        unmatchedDerivativeSum S T j k (fun ab ↦ T.signSupport ab.2 ⊆ S.signSupport ab.1) x := by
  let Q (y : InversionClass n → Bool) :=
    ∑ b, walshPartial (T.fieldCoefficient k) b y * walshPartial (S.fieldCoefficient j) b y
  let P := T.Assignment n × S.Assignment n
  let w (ab : P) := derivativePairWeight T S k j ab.1 ab.2
  let f (ab : P) (y : InversionClass n → Bool) := w ab * walsh (assignmentDifference T S ab.1 ab.2) y
  have hExpand (y : InversionClass n → Bool) : Q y = ∑ ab, f ab y := by
    simp only [P, Q, f, w, Fintype.sum_prod_type]
    exact sum_tree_partials_mul_eq T S k j y
  have hMean : average Q =
      ∑ ab : P, if T.signSupport ab.1 = S.signSupport ab.2 then w ab else 0 := by
    rw [funext hExpand, average_sum]
    simp only [f, average_mul_left, average_walsh, assignmentDifference,
      symmDiff_eq_empty, mul_ite, mul_one, mul_zero]
  have hSwap :
      unmatchedDerivativeSum S T j k (fun ab ↦ T.signSupport ab.2 ⊆ S.signSupport ab.1) x =
        ∑ ab : P, if (¬S.signSupport ab.2 ⊆ T.signSupport ab.1) ∧
          T.signSupport ab.1 ⊆ S.signSupport ab.2 then f ab x else 0 := by
    unfold unmatchedDerivativeSum
    refine Fintype.sum_equiv (Equiv.prodComm (S.Assignment n) (T.Assignment n)) _ _ ?_
    rintro ⟨a', a⟩
    simp only [f, w, Equiv.prodComm_apply, Prod.swap_prod_mk, derivativePairWeight,
      assignmentDifference]
    rw [inter_comm (S.signSupport a') (T.signSupport a),
      symmDiff_comm (S.signSupport a') (T.signSupport a),
      mul_comm (assignmentWeight S j a') (assignmentWeight T k a)]
    by_cases h : (¬S.signSupport a' ⊆ T.signSupport a) ∧ T.signSupport a ⊆ S.signSupport a' <;>
      simp [h]
  change Q x - average Q = _
  rw [hExpand x, hMean, hSwap, unmatchedDerivativeSum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro ab _
  by_cases hEq : T.signSupport ab.1 = S.signSupport ab.2
  · simp [hEq, f, assignmentDifference, walsh]
  by_cases hSub : T.signSupport ab.1 ⊆ S.signSupport ab.2
  · have hOther : ¬S.signSupport ab.2 ⊆ T.signSupport ab.1 := fun h ↦
      hEq (Subset.antisymm hSub h)
    simp [f, w, hEq, hSub, hOther]
  · simp [f, w, hEq, hSub]

/-- The variance of the normalized derivative pairing is bounded by the
two overlap-count constants divided by n. -/
theorem average_centered_treeDerivativePairing_sq_le (T S : RootedTree) (k j : ZMod n) :
    average (fun x ↦ (normalizedTreeDerivativePairing T S k j x -
      average (normalizedTreeDerivativePairing T S k j)) ^ 2) ≤
      (2 * (unmatchedDerivativeConstant T S + unmatchedDerivativeConstant S T)) / n := by
  let Q (x : InversionClass n → Bool) :=
    ∑ b, walshPartial (T.fieldCoefficient k) b x * walshPartial (S.fieldCoefficient j) b x
  let f := unmatchedDerivativeSum T S k j (fun _ ↦ True)
  let g := unmatchedDerivativeSum S T j k (fun ab ↦ T.signSupport ab.2 ⊆ S.signSupport ab.1)
  have hd : (1 : ℝ) ≤ T.nodeCount := by exact_mod_cast T.nodeCount_pos
  have hMean : average (normalizedTreeDerivativePairing T S k j) =
      average Q / T.nodeCount := by
    change average (fun x ↦ Q x / T.nodeCount) = _
    simp only [div_eq_inv_mul, average_mul_left]
  calc
    _ ≤ average (fun x ↦ (Q x - average Q) ^ 2) := by
      apply average_mono
      intro x
      rw [hMean]
      change (Q x / T.nodeCount - average Q / T.nodeCount) ^ 2 ≤ _
      rw [← sub_div, div_pow]
      exact div_le_self (sq_nonneg _) (one_le_pow₀ hd)
    _ = average (fun x ↦ (f x + g x) ^ 2) := by
      have hZ (x : InversionClass n → Bool) : Q x - average Q = f x + g x :=
        centered_treePartials_eq T S k j x
      simp_rw [hZ]
    _ ≤ 2 * (average (fun x ↦ f x ^ 2) + average (fun x ↦ g x ^ 2)) := by
      rw [← average_add, ← average_mul_left]
      exact average_mono fun x ↦ by nlinarith only [sq_nonneg (f x - g x)]
    _ ≤ 2 * (unmatchedDerivativeConstant T S / n + unmatchedDerivativeConstant S T / n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (average_unmatchedDerivativeSum_sq_le T S k j _)
          (average_unmatchedDerivativeSum_sq_le S T j k _)) (by norm_num)
    _ = _ := by rw [← add_div, ← mul_div_assoc]

end LovaszTheta.Circulant
