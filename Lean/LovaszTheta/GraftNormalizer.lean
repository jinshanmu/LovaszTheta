module

public import LovaszTheta.FiniteMultiplicity
public import LovaszTheta.GraftIsomorphism
public import LovaszTheta.TreeCovarianceEstimate

/-!
# Automorphism factors of grafts

An automorphism permutes isomorphic children and identifies each
child with its destination. Thus the automorphism count is the
product of the child automorphism counts and multiplicity factorials.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace LovaszTheta.Circulant.RootedTree

variable {I A : Type*} [Fintype I] [DecidableEq A] (S : I → RootedTree) (hI : Fintype.card I ≠ 1)

/-- Count automorphisms of a graft using a key that distinguishes
the child isomorphism types. -/
theorem card_automorphism_graft (f : I → A)
    (hf : ∀ i j, Nonempty ((S i).Isomorphism (S j)) ↔ f i = f j) :
    Fintype.card (graft S hI).Automorphism =
      (∏ a ∈ (familyMultiset f).toFinset, ((familyMultiset f).count a)!) *
        ∏ i, Fintype.card (S i).Automorphism := by
  have h (q : Equiv.Perm I) :
      (∏ i, Fintype.card ((S i).Isomorphism (S (q i)))) =
        if ∀ i, f (q i) = f i then ∏ i, Fintype.card (S i).Automorphism else 0 := by
    by_cases hq : ∀ i, f (q i) = f i
    · rw [ite_eq_left hq]
      exact prod_congr rfl fun i _ ↦ by
        obtain ⟨e⟩ := (hf i (q i)).mpr (hq i).symm
        exact (card_isomorphism_eq_card_automorphism e).trans e.card_automorphism_eq.symm
    · rw [ite_eq_right hq]
      push Not at hq
      obtain ⟨i,hi⟩ := hq
      let _ : IsEmpty ((S i).Isomorphism (S (q i))) :=
        not_nonempty_iff.mp (fun he ↦ hi ((hf i (q i)).mp he).symm)
      exact prod_eq_zero (mem_univ i) Fintype.card_of_isEmpty
  change Fintype.card ((graft S hI).Isomorphism (graft S hI)) = _
  rw [Fintype.card_congr (graftIsomorphismEquiv (hI := hI) (hJ := hI)), Fintype.card_sigma]
  simp_rw [Fintype.card_pi,h]
  rw [← sum_filter, sum_const, nsmul_eq_mul, ← Fintype.card_subtype, ← card_familyPerm]
  rfl

/-- The leaves of a nonempty graft give the sum of the leaf counts. -/
lemma card_leaf_graft [Nonempty I] :
    Fintype.card (graft S hI).Leaf = ∑ i, Fintype.card (S i).Leaf := by
  rw [← Fintype.card_congr (graftLeafEquiv S hI), Fintype.card_sigma]

end LovaszTheta.Circulant.RootedTree
