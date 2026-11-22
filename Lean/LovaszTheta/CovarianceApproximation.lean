module

public import LovaszTheta.CovarianceMatchingSum
public import LovaszTheta.RootMatchCounts

/-!
# The unrestricted covariance sum

Exceptional residues and nonpreserving signed permutations lose one
free leaf. The remaining sums are unrestricted character averages.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma abs_sum_sub_restricted_le {A : Type*} [Fintype A]
    (f : A → ℝ) (P : A → Prop) (C : ℝ) (hf : ∀ a, ¬P a → |f a| ≤ C) :
    |∑ a, f a - ∑ a, if P a then f a else 0| ≤ Fintype.card {a // ¬P a} * C := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ a, |f a - if P a then f a else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, if ¬P a then C else 0 := by
      apply sum_le_sum
      intro a _
      by_cases h : P a
      · simp [h]
      · simpa [h] using hf a h
    _ = _ := by
      rw [← sum_filter, Fintype.card_subtype]
      simp

private lemma abs_sum_rootPair_of_support_le (T S : RootedTree) (k j : ZMod n) (a : T.Assignment n) :
    |∑ b : S.Assignment n, if S.signSupport b = T.signSupport a then
      rootPair T S k j a.val b.val else 0| ≤ ((2 * S.nodeCount : ℕ) : ℝ)^Fintype.card S.Leaf := by
  rw [← sum_filter]
  calc
    _ ≤ ∑ b with S.signSupport b = T.signSupport a, |rootPair T S k j a.val b.val| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : S.Assignment n with S.signSupport b = T.signSupport a, (1 : ℝ) :=
      sum_le_sum fun b _ ↦ abs_rootPair_le T S k j a.val b.val
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast S.card_assignment_support_le (T.signSupport a)

private lemma abs_unnormalizedCovarianceSum_sub_regular_le (T S : RootedTree) (k j : ZMod n) :
    |unnormalizedCovarianceSum T S k j - regularCovarianceSum T S k j| ≤
      ((2*T.nodeCount + 2*T.nodeCount^2 : ℕ) : ℝ) *
        (n : ℝ)^(Fintype.card T.Leaf-1) * ((2*S.nodeCount : ℕ) : ℝ)^Fintype.card S.Leaf := by
  let f (a : T.Assignment n) := ∑ b : S.Assignment n,
    if S.signSupport b = T.signSupport a then rootPair T S k j a.val b.val else 0
  have hEq : regularCovarianceSum T S k j =
      ∑ a : T.Assignment n, if RegularAssignment T a.val then f a else 0 := by
    rw [regularCovarianceSum, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    by_cases h : RegularAssignment T a.val <;> simp [h, f]
  let A := {a : T.Assignment n // ¬ RegularAssignment T a.val}
  let g (a : A) : {a : T.Leaf → ZMod n // ¬RegularAssignment T a} := ⟨a.val.val, a.property⟩
  have hg : Function.Injective g := fun a b he ↦ Subtype.ext (Subtype.ext
    (congrArg (fun z : {a : T.Leaf → ZMod n // ¬RegularAssignment T a} ↦ z.val) he))
  have hCount := (Fintype.card_le_of_injective g hg).trans (card_not_regularAssignment_le (n := n) T)
  have hCount' : (Fintype.card A : ℝ) ≤
      ((2*T.nodeCount + 2*T.nodeCount^2 : ℕ) : ℝ) * (n : ℝ)^(Fintype.card T.Leaf-1) := by
    exact_mod_cast hCount
  rw [hEq, unnormalizedCovarianceSum, Fintype.sum_prod_type]
  exact (abs_sum_sub_restricted_le f _ _ fun a _ ↦ abs_sum_rootPair_of_support_le T S k j a).trans
    (mul_le_mul_of_nonneg_right hCount' (by positivity))

namespace SignedNodeMatch

variable {T S : RootedTree}

lemma abs_sourcePair_le (M : SignedNodeMatch T S) (k j : ZMod n) (a : T.Leaf → ZMod n) :
    |M.sourcePair k j a| ≤ 1 := by
  have h (r : ZMod n) : |(ZMod.stdAddChar r).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [ZMod.stdAddChar_apply, Circle.norm_coe])
  rw [sourcePair, abs_mul, ← mul_one (1 : ℝ)]
  exact mul_le_mul (h _) (h _) (abs_nonneg _) zero_le_one

/-- Extend a preserving match to all source assignments. -/
noncomputable def unrestrictedContribution (M : SignedNodeMatch T S) (k j : ZMod n) : ℝ :=
  if M.PreservesParentSums then ∑ a : T.Leaf → ZMod n, M.sourcePair k j a else 0

lemma abs_covarianceSum_sub_unrestricted_le (M : SignedNodeMatch T S) (k j : ZMod n) :
    |M.covarianceSum k j - M.unrestrictedContribution k j| ≤
      ((2*T.nodeCount + 2*T.nodeCount^2 + (S.nodeCount + 1) : ℕ) : ℝ) *
        (n : ℝ)^(Fintype.card T.Leaf - 1) := by
  by_cases h : M.PreservesParentSums
  · rw [unrestrictedContribution, ite_eq_left h, covarianceSum_eq_sum_source M h, abs_sub_comm]
    let P := RegularAssignment (n := n) T
    have hEq : (∑ a : {a // P a}, M.sourcePair k j a.val) =
        ∑ a, if P a then M.sourcePair k j a else 0 := by
      rw [← sum_filter]
      exact (Finset.sum_subtype (univ.filter P) (p := P) (fun _ ↦ by simp) (M.sourcePair k j)).symm
    rw [hEq]
    refine (abs_sum_sub_restricted_le _ P 1 fun a _ ↦ M.abs_sourcePair_le k j a).trans ?_
    rw [mul_one]
    exact_mod_cast (card_not_regularAssignment_le (n := n) T).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · rw [unrestrictedContribution, ite_eq_right h, sub_zero, covarianceSum]
    let A := {ab : (T.Leaf → ZMod n) × (S.Leaf → ZMod n) // M.Matches ab.1 ab.2}
    let g (ab : M.RegularPairs n) : A := ⟨ab.val, ab.property.2⟩
    have hg : Function.Injective g := fun a b he ↦ Subtype.ext (congrArg (fun z : A ↦ z.val) he)
    have hCount := (Fintype.card_le_of_injective g hg).trans (M.card_matches_le_of_not_preserves (n := n) h)
    calc
      _ ≤ ∑ ab : M.RegularPairs n, |rootPair T S k j ab.val.1 ab.val.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ ab : M.RegularPairs n, (1 : ℝ) :=
        sum_le_sum fun ab _ ↦ abs_rootPair_le T S k j ab.val.1 ab.val.2
      _ ≤ _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
        exact_mod_cast hCount.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

end SignedNodeMatch

/-- Counts of omitted assignments and bad node permutations in the
unnormalized covariance calculation. -/
noncomputable def covarianceError (T S : RootedTree) : ℝ :=
  ((2*T.nodeCount + 2*T.nodeCount^2 : ℕ) : ℝ) *
    ((2*S.nodeCount : ℕ) : ℝ)^Fintype.card S.Leaf +
  ((2*T.nodeCount : ℕ) : ℝ)^S.nodeCount *
    ((2*T.nodeCount + 2*T.nodeCount^2 + (S.nodeCount + 1) : ℕ) : ℝ)

/-- The error in extending the preserving matches to unrestricted
leaf assignments is bounded by their count times one fewer free leaf. -/
theorem abs_unnormalizedCovarianceSum_sub_unrestricted_le (T S : RootedTree) (k j : ZMod n) :
    |unnormalizedCovarianceSum T S k j -
      ∑ M : SignedNodeMatch T S, M.unrestrictedContribution k j| ≤
      covarianceError T S * (n : ℝ)^(Fintype.card T.Leaf-1) := by
  let Q := (n : ℝ)^(Fintype.card T.Leaf-1)
  let B := ((2*T.nodeCount + 2*T.nodeCount^2 + (S.nodeCount + 1) : ℕ) : ℝ)
  have h := abs_sub_le (unnormalizedCovarianceSum T S k j) (regularCovarianceSum T S k j)
    (∑ M : SignedNodeMatch T S, M.unrestrictedContribution k j)
  have hErr :
      |regularCovarianceSum T S k j - ∑ M : SignedNodeMatch T S, M.unrestrictedContribution k j| ≤
        ((2*T.nodeCount : ℕ) : ℝ)^S.nodeCount * (B*Q) := by
    rw [regularCovarianceSum_eq_sum_matches, ← sum_sub_distrib]
    calc
      _ ≤ ∑ M : SignedNodeMatch T S, |M.covarianceSum k j - M.unrestrictedContribution k j| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _M : SignedNodeMatch T S, B*Q :=
        sum_le_sum fun M _ ↦ M.abs_covarianceSum_sub_unrestricted_le k j
      _ = (Fintype.card (SignedNodeMatch T S) : ℝ) * (B*Q) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast SignedNodeMatch.card_le T S)
        (by unfold B Q; positivity)
  refine (h.trans (add_le_add (abs_unnormalizedCovarianceSum_sub_regular_le T S k j) hErr)).trans_eq ?_
  unfold covarianceError B Q
  ring

end LovaszTheta.Circulant
