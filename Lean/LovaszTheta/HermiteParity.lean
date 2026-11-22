module

public import LovaszTheta.HermiteCompleteness

/-!
# Parity of the Hermite coefficients

The Hermite recursion alternates parity. The centered Gaussian
law is invariant under negation, so the coefficients of odd order
vanish for an even function.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Polynomial
open scoped NNReal

namespace LovaszTheta.Circulant

lemma realHermite_eval_neg (j : ℕ) (x : ℝ) :
    (realHermite j).eval (-x) = (-1 : ℝ)^j * (realHermite j).eval x := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j ih₀ ih₁ =>
    have hRec (y : ℝ) : (realHermite (j+2)).eval y =
        y*(realHermite (j+1)).eval y - ((j : ℝ)+1)*(realHermite j).eval y := by
      rw [show j+2 = j+1+1 by omega, realHermite_succ (j+1), derivative_realHermite_succ]
      simp only [eval_sub, eval_mul, eval_X, eval_C]
    rw [hRec (-x), ih₀, ih₁, hRec x, show j+2 = j+1+1 by omega, pow_succ (-1 : ℝ) (j+1),
      pow_succ (-1 : ℝ) j]
    ring

lemma normalizedHermite_eval_neg (j : ℕ) (x : ℝ) :
    normalizedHermite j (-x) = (-1 : ℝ)^j * normalizedHermite j x := by
  rw [normalizedHermite, realHermite_eval_neg, mul_div_assoc]
  rfl

lemma continuous_normalizedHermite (j : ℕ) : Continuous (normalizedHermite j) := by
  unfold normalizedHermite
  fun_prop

/-- An even function has zero odd Hermite coefficients. -/
theorem hermiteCoefficient_eq_zero_of_odd_of_even {f : ℝ → ℝ} (hC : Continuous f)
    (hf : f.Even) {j : ℕ} (hj : Odd j) :
    hermiteCoefficient f j = 0 := by
  have hP : Continuous (fun x ↦ f x*normalizedHermite j x) :=
    hC.mul (continuous_normalizedHermite j)
  have h := integral_map (μ := gaussianReal 0 (1 : ℝ≥0)) (φ := fun x : ℝ ↦ -x)
    (by fun_prop) hP.aestronglyMeasurable
  rw [gaussianReal_map_neg, neg_zero] at h
  have hEven (x : ℝ) : f (-x)*normalizedHermite j (-x) = -(f x*normalizedHermite j x) := by
    rw [hf, normalizedHermite_eval_neg, hj.neg_one_pow, neg_one_mul, mul_neg]
  simp_rw [hEven, integral_neg] at h
  unfold hermiteCoefficient
  linarith only [h]

end LovaszTheta.Circulant
