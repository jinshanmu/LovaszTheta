module

public import LovaszTheta.GaussianIntegration

/-!
# Gaussian even moments

Integration by parts gives the even-moment recursion. Bounding each
factor by the highest order gives the moment bound in the comparison.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LovaszTheta.Circulant

/-- The centered Gaussian even-moment recursion, including zero variance. -/
theorem integral_pow_gaussian_succ (v : ℝ≥0) (m : ℕ) :
    (∫ x, x^(2*(m+1)) ∂gaussianReal 0 v) =
      (v : ℝ) * (2*(m : ℝ)+1) * ∫ x, x^(2*m) ∂gaussianReal 0 v := by
  let p := 2*m+1
  let f (x : ℝ) := x^p
  let g (x : ℝ) := (p : ℝ) * x^(2*m)
  have hd (x : ℝ) : HasDerivAt f (g x) x := by
    convert (hasDerivAt_id' x).pow p using 1
    simp [g, p]
  have hgp : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have habs (x : ℝ) (k : ℕ) (hk : k ≤ p) : |x^k| ≤ (1+|x|)^p := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x]) hk)
  have h := gaussian_integration_by_parts v p p hd (by unfold g; fun_prop)
    (fun x ↦ (habs x p le_rfl).trans (le_mul_of_one_le_left (by positivity) hgp))
    (fun x ↦ by
      change |(p : ℝ) * x^(2*m)| ≤ _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p)]
      exact mul_le_mul_of_nonneg_left (habs x (2*m) (by omega)) (by positivity))
  have hMul (x : ℝ) : x * f x = x^(2*(m+1)) := by
    change x * x^p = _
    rw [← pow_succ', show p+1 = 2*(m+1) by omega]
  simp only [hMul, g, integral_const_mul, ← mul_assoc, p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] at h
  exact h

/-- The even absolute moments are bounded by the powers of the
variance times the moment order. -/
theorem integral_abs_pow_gaussian_le (v : ℝ≥0) (m : ℕ) :
    (∫ x, |x|^(2*m) ∂gaussianReal 0 v) ≤ ((2*m : ℝ) * (v : ℝ))^m := by
  have hEven (k : ℕ) (x : ℝ) : |x|^(2*k) = x^(2*k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  simp only [hEven]
  induction m with
  | zero => simp
  | succ m h =>
    rw [integral_pow_gaussian_succ]
    have hv : (0 : ℝ) ≤ (v : ℝ) := by positivity
    have h₁ : (v : ℝ)*(2*(m : ℝ)+1) ≤ 2*(m+1 : ℕ)*(v : ℝ) := by
      push_cast
      nlinarith only [hv]
    calc
      _ ≤ (v : ℝ)*(2*(m : ℝ)+1) * ((2*m : ℝ) * v)^m :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ (2*(m+1 : ℕ)*(v : ℝ)) * (2*(m+1 : ℕ)*(v : ℝ))^m := by
        refine mul_le_mul h₁ (pow_le_pow_left₀ (by positivity) ?_ m) (by positivity) (by positivity)
        push_cast
        nlinarith only [hv]
      _ = _ := by rw [pow_succ']

end LovaszTheta.Circulant
