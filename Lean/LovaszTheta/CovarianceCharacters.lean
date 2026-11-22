module

public import LovaszTheta.CovarianceApproximation

/-!
# Evaluation of the preserving matches

The target root either matches a proper subtree, whose residue
is independent of the root residue, or matches the source root.
The latter matches are counted by rooted isomorphisms and orientations.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

namespace SignedNodeMatch

variable {T S : RootedTree}

private lemma sourcePair_eq_character_product (M : SignedNodeMatch T S) (k j : ZMod n)
    (a : T.Leaf → ZMod n) :
    M.sourcePair k j a = (ZMod.stdAddChar (-(T.residue a T.root * k))).re *
      (ZMod.stdAddChar (-(T.residue a (M.node S.root) * j))).re := by
  unfold sourcePair value
  split_ifs
  · rfl
  · simp only [neg_mul, neg_neg, re_stdAddChar_neg]

private lemma average_sourcePair (M : SignedNodeMatch T S) (k j : ZMod n)
    (hk : RegularFrequency k) :
    average (M.sourcePair k j) =
      if M.node S.root = T.root then if j = k ∨ j = -k then 1/2 else 0 else 0 := by
  change average (fun a ↦ M.sourcePair k j a) = _
  simp_rw [sourcePair_eq_character_product]
  by_cases hRoot : M.node S.root = T.root
  · simpa [hRoot] using average_root_character_pair T k j hk
  · have hNonzero : k ≠ 0 := fun he ↦ hk (by rw [he, mul_zero])
    simpa only [hRoot, ite_false] using
      average_root_nonroot_character_eq_zero T _ hRoot k j hNonzero

private lemma unrestrictedContribution_eq (M : SignedNodeMatch T S) (k j : ZMod n)
    (hk : RegularFrequency k) :
    M.unrestrictedContribution k j =
      if M.PreservesParentSums ∧ M.node S.root = T.root then
        (n : ℝ)^Fintype.card T.Leaf * (if j = k ∨ j = -k then 1/2 else 0) else 0 := by
  have h := M.average_sourcePair k j hk
  simp only [average, Fintype.card_fun, ZMod.card, Nat.cast_pow] at h
  have hn : 0 < (n : ℝ) ^ Fintype.card T.Leaf := by
    have : n ≠ 0 := NeZero.ne n
    positivity
  have hSum := (div_eq_iff (ne_of_gt hn)).mp h
  unfold unrestrictedContribution
  by_cases hb : M.PreservesParentSums <;> by_cases hr : M.node S.root = T.root <;>
    simp [hb, hr, hSum, mul_comm]

end SignedNodeMatch

/-- The exact contribution from preserving matches in the
unrestricted sum. -/
theorem sum_unrestrictedContribution (T S : RootedTree) (k j : ZMod n)
    (hk : RegularFrequency k) (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) :
    (∑ M : SignedNodeMatch T S, M.unrestrictedContribution k j) =
      (n : ℝ)^Fintype.card T.Leaf * Fintype.card (S.Isomorphism T) *
        (if j = k ∨ j = -k then 1 else 0) := by
  have hCount : Fintype.card {M : SignedNodeMatch T S //
      M.PreservesParentSums ∧ M.node S.root = T.root} = Fintype.card (S.Isomorphism T) * 2 := by
    rw [Fintype.card_congr (SignedNodeMatch.rootPreservingEquiv hL), Fintype.card_prod, Fintype.card_bool]
  have hFilter : (univ.filter (fun M : SignedNodeMatch T S ↦
      M.PreservesParentSums ∧ M.node S.root = T.root)).card = Fintype.card (S.Isomorphism T) * 2 :=
    (Fintype.card_subtype _).symm.trans hCount
  simp_rw [SignedNodeMatch.unrestrictedContribution_eq _ k j hk]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hFilter, Nat.cast_mul, Nat.cast_ofNat]
  split_ifs <;> ring

end LovaszTheta.Circulant
