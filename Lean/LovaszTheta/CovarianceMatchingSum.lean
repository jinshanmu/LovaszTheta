module

public import LovaszTheta.RegularSignedMatches
public import LovaszTheta.TreeCovariance
public import LovaszTheta.UniformLeafSums

/-!
# Reindexing the covariance by signed node permutations

After removing singleton inversion classes, the signed permutation
is unique. A match preserving the parent identities contributes
one target assignment for each regular source assignment.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The product of root characters of two assignments before standardization. -/
noncomputable def rootPair (T S : RootedTree) (k j : ZMod n)
    (a : T.Leaf → ZMod n) (b : S.Leaf → ZMod n) : ℝ :=
  (ZMod.stdAddChar (-(T.residue a T.root * k))).re *
    (ZMod.stdAddChar (-(S.residue b S.root * j))).re

lemma abs_rootPair_le (T S : RootedTree) (k j : ZMod n)
    (a : T.Leaf → ZMod n) (b : S.Leaf → ZMod n) :
    |rootPair T S k j a b| ≤ 1 := by
  have h (r : ZMod n) : |(ZMod.stdAddChar r).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [ZMod.stdAddChar_apply, Circle.norm_coe])
  rw [rootPair, abs_mul, ← mul_one (1 : ℝ)]
  exact mul_le_mul (h _) (h _) (abs_nonneg _) zero_le_one

/-- The full-support covariance sum before removing singleton classes. -/
noncomputable def unnormalizedCovarianceSum (T S : RootedTree) (k j : ZMod n) : ℝ :=
  ∑ ab : T.Assignment n × S.Assignment n, if S.signSupport ab.2 = T.signSupport ab.1 then
    rootPair T S k j ab.1.val ab.2.val else 0

lemma average_field_mul_eq_normalizers_mul (T S : RootedTree) (k j : ZMod n) :
    average (fun x ↦ T.field x k * S.field x j) =
      (T.fieldNormalizer n * S.fieldNormalizer n) * unnormalizedCovarianceSum T S k j := by
  rw [average_field_mul_eq_sum_matches]
  simp only [unnormalizedCovarianceSum, Fintype.sum_prod_type, mul_sum, mul_ite, mul_zero]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by
    split_ifs <;> simp [assignmentWeight, rootPair, mul_assoc, mul_left_comm]

/-- The covariance sum over pairs without singleton classes. -/
noncomputable def regularCovarianceSum (T S : RootedTree) (k j : ZMod n) : ℝ :=
  ∑ ab : T.Assignment n × S.Assignment n,
    if RegularAssignment T ab.1.val ∧ S.signSupport ab.2 = T.signSupport ab.1 then
      rootPair T S k j ab.1.val ab.2.val else 0

/-- The source-regular assignment pairs matching a given signed permutation. -/
abbrev SignedNodeMatch.RegularPairs {T S : RootedTree} (M : SignedNodeMatch T S) (n : ℕ) :=
  {ab : (T.Leaf → ZMod n) × (S.Leaf → ZMod n) // RegularAssignment T ab.1 ∧ M.Matches ab.1 ab.2}

/-- The unnormalized covariance contribution of a signed permutation. -/
noncomputable def SignedNodeMatch.covarianceSum {T S : RootedTree}
    (M : SignedNodeMatch T S) (k j : ZMod n) : ℝ :=
  ∑ ab : M.RegularPairs n, rootPair T S k j ab.val.1 ab.val.2

private lemma covarianceSum_eq_filtered {T S : RootedTree}
    (M : SignedNodeMatch T S) (k j : ZMod n) :
    M.covarianceSum k j = ∑ ab : T.Assignment n × S.Assignment n,
      if RegularAssignment T ab.1.val ∧ M.Matches ab.1.val ab.2.val then
        rootPair T S k j ab.1.val ab.2.val else 0 := by
  let p (ab : T.Assignment n × S.Assignment n) :=
    RegularAssignment T ab.1.val ∧ M.Matches ab.1.val ab.2.val
  let e : M.RegularPairs n ≃ {ab // p ab} :=
    { toFun := fun ab ↦
        ⟨(⟨ab.val.1, ab.property.1.1⟩,
          ⟨ab.val.2, (M.regularAssignment_of_matches ab.property.1 ab.property.2).1⟩),
          ab.property⟩
      invFun := fun ab ↦ ⟨(ab.val.1.val, ab.val.2.val), ab.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold SignedNodeMatch.covarianceSum
  rw [← sum_filter]
  calc
    _ = ∑ ab : {ab // p ab}, rootPair T S k j ab.val.1.val ab.val.2.val :=
      Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = _ := (Finset.sum_subtype (univ.filter p) (p := p) (fun _ ↦ by simp)
      (fun ab ↦ rootPair T S k j ab.1.val ab.2.val)).symm

/-- The regular covariance contribution splits exactly into the signed
node permutations. -/
theorem regularCovarianceSum_eq_sum_matches (T S : RootedTree) (k j : ZMod n) :
    regularCovarianceSum T S k j = ∑ M : SignedNodeMatch T S, M.covarianceSum k j := by
  unfold regularCovarianceSum
  simp_rw [covarianceSum_eq_filtered]
  rw [sum_comm]
  apply sum_congr rfl
  intro ab _
  by_cases hA : RegularAssignment T ab.1.val
  · by_cases hI : S.signSupport ab.2 = T.signSupport ab.1
    · obtain ⟨M, hM, hUnique⟩ := SignedNodeMatch.existsUnique_of_equal_support ab.1 ab.2 hA hI
      rw [Finset.sum_eq_single M]
      · simp [hA, hI, hM]
      · intro N _ hne
        have hN : ¬ N.Matches ab.1.val ab.2.val := fun he ↦ hne (hUnique N he)
        simp [hN]
      · intro h
        exact (h (mem_univ _)).elim
    · have hN (M : SignedNodeMatch T S) : ¬M.Matches ab.1.val ab.2.val := fun hm ↦
        hI (M.signSupport_eq_of_matches ab.1 ab.2 hm)
      simp [hI, hN]
  · simp [hA]

/-- Under a preserving permutation, the target root character is the
matched source residue's character with its indicated orientation. -/
noncomputable def SignedNodeMatch.sourcePair {T S : RootedTree}
    (M : SignedNodeMatch T S) (k j : ZMod n) (a : T.Leaf → ZMod n) : ℝ :=
  (ZMod.stdAddChar (-(T.residue a T.root * k))).re *
    (ZMod.stdAddChar (-(M.value a S.root * j))).re

/-- A preserving match contributes exactly one target for every regular
source assignment. -/
theorem SignedNodeMatch.covarianceSum_eq_sum_source {T S : RootedTree}
    (M : SignedNodeMatch T S) (h : M.PreservesParentSums) (k j : ZMod n) :
    M.covarianceSum k j =
      ∑ a : {a : T.Leaf → ZMod n // RegularAssignment T a}, M.sourcePair k j a.val := by
  let e : {a : T.Leaf → ZMod n // RegularAssignment T a} ≃ M.RegularPairs n :=
    { toFun := fun a ↦ ⟨(a.val, fun i ↦ M.value a.val i.val), a.property, M.matches_of_preserves h a.val⟩
      invFun := fun ab ↦ ⟨ab.val.1, ab.property.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun ab ↦ Subtype.ext (Prod.ext rfl
        (M.target_eq_of_matches (M.matches_of_preserves h ab.val.1) ab.property.2)) }
  unfold SignedNodeMatch.covarianceSum
  exact (Fintype.sum_equiv e _ _ fun a ↦ by
    unfold SignedNodeMatch.sourcePair rootPair
    have hh := M.matches_of_preserves h a.val S.root
    change _ = (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re *
      (ZMod.stdAddChar (-(S.residue (fun i ↦ M.value a.val i.val) S.root * j))).re
    rw [hh]).symm

end LovaszTheta.Circulant
