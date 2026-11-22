module

public import LovaszTheta.GraftTopDegree

/-!
# Normalization of the leading graft term

Leaf powers of the modulus cancel between the graft and its
children. The automorphism ratio leaves only the square root
of the product of the child multiplicity factorials.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace LovaszTheta.Circulant.RootedTree

variable {I A : Type*} [Fintype I] [Nonempty I] [DecidableEq A]

/-- The normalization ratio is exactly the Hermite leading coefficient denominator. -/
theorem fieldNormalizer_graft_ratio (S : I → RootedTree) (hI : Fintype.card I ≠ 1)
    (f : I → A) (hf : ∀ i j, Nonempty ((S i).Isomorphism (S j)) ↔ f i = f j)
    (n : ℕ) [NeZero n] :
    (∏ i, (S i).fieldNormalizer n) / (graft S hI).fieldNormalizer n =
      ∏ a ∈ (familyMultiset f).toFinset, Real.sqrt ((familyMultiset f).count a).factorial := by
  let G := graft S hI
  have hN : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hLeaves : Real.sqrt ((n : ℝ)^Fintype.card G.Leaf) =
      ∏ i, Real.sqrt ((n : ℝ)^Fintype.card (S i).Leaf) := by
    rw [card_leaf_graft, ← prod_pow_eq_pow_sum, Real.sqrt_prod _ (fun _ _ ↦ by positivity)]
  have hAut : Real.sqrt (Fintype.card G.Automorphism) =
      (∏ a ∈ (familyMultiset f).toFinset, Real.sqrt ((familyMultiset f).count a).factorial) *
        ∏ i, Real.sqrt (Fintype.card (S i).Automorphism) := by
    rw [card_automorphism_graft S hI f hf, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod,
      Real.sqrt_mul (by positivity), Real.sqrt_prod _ (fun _ _ ↦ by positivity),
      Real.sqrt_prod _ (fun _ _ ↦ by positivity)]
  have hPos (i : I) : 0 < Real.sqrt (Fintype.card (S i).Automorphism) :=
    Real.sqrt_pos_of_pos (Nat.cast_pos.mpr Fintype.card_pos)
  have hX : (∏ i, Real.sqrt ((n : ℝ)^Fintype.card (S i).Leaf)) ≠ 0 := by positivity
  have hY : (∏ i, Real.sqrt (Fintype.card (S i).Automorphism)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ ↦ (hPos i).ne'
  simp only [fieldNormalizer,Finset.prod_inv_distrib,Finset.prod_mul_distrib]
  rw [hLeaves, hAut, div_inv_eq_mul]
  field_simp

end LovaszTheta.Circulant.RootedTree
