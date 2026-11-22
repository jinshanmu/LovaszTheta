module

public import LovaszTheta.TreeMoments
public import LovaszTheta.TreeOverlapMoments

/-!
# Walsh expansion of the tree derivative pairing

Differentiating two sign monomials at a common class removes that
class from both. Their product retains exactly the symmetric
difference, with multiplicity given by the number of possible
common differentiated classes.
-/

@[expose] public section

open Finset
open scoped Classical symmDiff

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The real weight of one admissible assignment in a tree field. -/
noncomputable def assignmentWeight (T : RootedTree) (k : ZMod n) (a : T.Assignment n) : ℝ :=
  T.fieldNormalizer n * (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re

lemma abs_assignmentWeight_le (T : RootedTree) (k : ZMod n) (a : T.Assignment n) :
    |assignmentWeight T k a| ≤ T.fieldNormalizer n := by
  have hN : 0 ≤ T.fieldNormalizer n := by unfold RootedTree.fieldNormalizer; positivity
  unfold assignmentWeight
  rw [abs_mul, abs_of_nonneg hN]
  have hRoot : |(ZMod.stdAddChar (-(T.residue a.val T.root * k))).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [ZMod.stdAddChar_apply, Circle.norm_coe])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hRoot hN

private lemma fieldCoefficient_eq_sum_weights (T : RootedTree) (k : ZMod n)
    (I : Finset (InversionClass n)) :
    T.fieldCoefficient k I =
      ∑ a : T.Assignment n, if T.signSupport a = I then assignmentWeight T k a else 0 := by
  simp only [RootedTree.fieldCoefficient, assignmentWeight, mul_sum, mul_ite, mul_zero]

private lemma walshPartial_tree_eq_sum (T : RootedTree) (k : ZMod n) (b : InversionClass n)
    (x : InversionClass n → Bool) :
    walshPartial (T.fieldCoefficient k) b x =
      ∑ a : T.Assignment n, if b ∈ T.signSupport a then
        assignmentWeight T k a * walsh ((T.signSupport a).erase b) x else 0 := by
  have hTerm (I : Finset (InversionClass n)) :
      (if b ∈ I then T.fieldCoefficient k I * walsh (I.erase b) x else 0) =
        ∑ a : T.Assignment n, if I = T.signSupport a then
          (if b ∈ I then assignmentWeight T k a * walsh (I.erase b) x else 0) else 0 := by
    by_cases h : b ∈ I
    · simp only [h, ite_true, fieldCoefficient_eq_sum_weights, sum_mul, ite_mul, zero_mul]
      exact sum_congr rfl fun a _ ↦ by
        by_cases ha : T.signSupport a = I
        · simp [ha]
        · simp [ha, Ne.symm ha]
    · simp [h]
  unfold walshPartial
  simp_rw [hTerm]
  rw [sum_comm]
  simp

/-- The multiplicity and weight of one pair in the unnormalized derivative
pairing. -/
noncomputable def derivativePairWeight (T S : RootedTree) (k j : ZMod n)
    (a : T.Assignment n) (b : S.Assignment n) : ℝ :=
  ((T.signSupport a ∩ S.signSupport b).card : ℝ) *
    (assignmentWeight T k a * assignmentWeight S j b)

lemma abs_derivativePairWeight_le (T S : RootedTree) (k j : ZMod n)
    (a : T.Assignment n) (b : S.Assignment n) :
    |derivativePairWeight T S k j a b| ≤
      (T.nodeCount : ℝ) * (T.fieldNormalizer n * S.fieldNormalizer n) := by
  have hT : 0 ≤ T.fieldNormalizer n := by unfold RootedTree.fieldNormalizer; positivity
  have hS : 0 ≤ S.fieldNormalizer n := by unfold RootedTree.fieldNormalizer; positivity
  have hOverlap : ((T.signSupport a ∩ S.signSupport b).card : ℝ) ≤ T.nodeCount := by
    exact_mod_cast (card_le_card (inter_subset_left (s₁ := T.signSupport a) (s₂ := S.signSupport b))).trans_eq
      (T.signSupport_card a)
  have hWeights := mul_le_mul (abs_assignmentWeight_le T k a) (abs_assignmentWeight_le S j b)
    (abs_nonneg _) hT
  unfold derivativePairWeight
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  exact mul_le_mul hOverlap hWeights (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)

omit [NeZero n] in
private lemma walsh_erase_mul {b : InversionClass n} {s t : Finset (InversionClass n)}
    (hs : b ∈ s) (ht : b ∈ t) (x : InversionClass n → Bool) :
    walsh (s.erase b) x * walsh (t.erase b) x = walsh (s ∆ t) x := by
  have hErase (r : Finset (InversionClass n)) (hr : b ∈ r) :
      walsh r x = sign (x b) * walsh (r.erase b) x := by
    unfold walsh
    rw [prod_eq_mul_prod_sdiff_singleton_of_mem hr, sdiff_singleton_eq_erase]
  rw [← walsh_mul, hErase s hs, hErase t ht, mul_mul_mul_comm, ← pow_two, sign_sq, one_mul]

/-- The derivative pairing is a weighted Walsh sum indexed by assignment
pairs. Each sign support is the symmetric difference of the two supports. -/
theorem sum_tree_partials_mul_eq (T S : RootedTree) (k j : ZMod n)
    (x : InversionClass n → Bool) :
    (∑ b, walshPartial (T.fieldCoefficient k) b x * walshPartial (S.fieldCoefficient j) b x) =
      ∑ a : T.Assignment n, ∑ a' : S.Assignment n,
        derivativePairWeight T S k j a a' * walsh (assignmentDifference T S a a') x := by
  have h (b : InversionClass n) (a : T.Assignment n) (a' : S.Assignment n) :
      (if b ∈ T.signSupport a then assignmentWeight T k a * walsh ((T.signSupport a).erase b) x else 0) *
        (if b ∈ S.signSupport a' then assignmentWeight S j a' * walsh ((S.signSupport a').erase b) x else 0) =
      if b ∈ T.signSupport a ∩ S.signSupport a' then
        (assignmentWeight T k a * assignmentWeight S j a') *
          walsh (assignmentDifference T S a a') x else 0 := by
    by_cases hT : b ∈ T.signSupport a <;> by_cases hS : b ∈ S.signSupport a'
    · simp only [hT, hS, mem_inter, true_and, ite_true]
      rw [mul_mul_mul_comm, walsh_erase_mul hT hS]
      rfl
    all_goals simp [hT, hS]
  simp_rw [walshPartial_tree_eq_sum, sum_mul, mul_sum, h]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro a' _
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  simp only [derivativePairWeight, mul_assoc]

end LovaszTheta.Circulant
