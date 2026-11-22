module

public import LovaszTheta.Signs
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Walsh moment estimates by support multiplicity

Grouping the summands by Walsh support bounds the squared norm by the
largest coefficient times the sum of absolute coefficients. This is
the estimate used for each overlap pattern of two tree assignments.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- Bound the second moment of a weighted Walsh sum by the maximum
multiplicity of a support and the total number of summands. -/
theorem average_walsh_sum_sq_le_of_multiplicity {ι X : Type*} [Fintype ι] [Fintype X]
    (s : X → Finset ι) (w : X → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ a, |w a| ≤ W) (M : ℕ)
    (hM : ∀ I : Finset ι, (univ.filter fun a ↦ s a = I).card ≤ M) :
    average (fun x : ι → Bool ↦ (∑ a, w a * walsh (s a) x) ^ 2) ≤
      W ^ 2 * M * Fintype.card X := by
  let F (I : Finset ι) := univ.filter fun a ↦ s a = I
  let c (I : Finset ι) := ∑ a ∈ F I, w a
  have hExpand (x : ι → Bool) : (∑ a, w a * walsh (s a) x) = walshCombination c x := by
    unfold walshCombination
    simp only [c, F, sum_mul, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    simp
  have hCoeff (I : Finset ι) : |c I| ≤ W * (F I).card := by
    unfold c
    calc
      _ ≤ ∑ a ∈ F I, |w a| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ F I, W := sum_le_sum fun a _ ↦ hw a
      _ = _ := by simp [mul_comm]
  have hOne (I : Finset ι) : c I ^ 2 ≤ (W ^ 2 * M) * (F I).card := by
    have hCard : ((F I).card : ℝ) ≤ M := by exact_mod_cast hM I
    have hMax := (hCoeff I).trans (mul_le_mul_of_nonneg_left hCard hW)
    calc
      _ = |c I| * |c I| := by rw [← pow_two, sq_abs]
      _ ≤ (W * M) * (W * (F I).card) :=
        mul_le_mul hMax (hCoeff I) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hCount : (∑ I, (F I).card) = Fintype.card X := by
    simp only [F, card_filter]
    rw [sum_comm]
    simp
  simp_rw [hExpand, pow_two, average_walshCombination_mul]
  calc
    _ ≤ ∑ I, (W ^ 2 * M) * (F I).card := sum_le_sum fun I _ ↦ by
      simpa only [pow_two] using hOne I
    _ = _ := by rw [← mul_sum, ← Nat.cast_sum, hCount, pow_two]

/-- The squared moment of the sum over patterns is bounded using the
finite (L^2) triangle inequality and Cauchy--Schwarz. -/
theorem average_sum_sq_le_card_mul_sum {I Ω : Type*} [Fintype I] [Fintype Ω]
    (f : I → Ω → ℝ) :
    average (fun x ↦ (∑ i, f i x) ^ 2) ≤
      (Fintype.card I : ℝ) * ∑ i, average (fun x ↦ f i x ^ 2) := by
  rw [← average_sum, ← average_mul_left]
  apply average_mono
  intro x
  simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i ↦ f i x)

end LovaszTheta.Circulant
