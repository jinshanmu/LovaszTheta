module

public import LovaszTheta.GaussianIntegration
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Hermite orthogonality for the standard Gaussian

The polynomial recursion and Gaussian integration by parts give
the lowering identity. Repeating it gives the squared Hermite norms
and orthogonality in the normalization of the manuscript.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Polynomial
open scoped Polynomial NNReal

namespace LovaszTheta.Circulant

/-- The probabilists' Hermite polynomial over the reals. -/
noncomputable def realHermite (j : ℕ) : ℝ[X] :=
  (Polynomial.hermite j).map (Int.castRingHom ℝ)

@[simp]
lemma realHermite_zero : realHermite 0 = 1 := by simp [realHermite]

@[simp]
lemma realHermite_one : realHermite 1 = X := by simp [realHermite]

lemma realHermite_succ (j : ℕ) : realHermite (j+1) = X*realHermite j - (realHermite j).derivative := by
  simp only [realHermite, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.derivative_map]

/-- The derivative lowers the degree with the factor j+1. -/
theorem derivative_realHermite_succ (j : ℕ) :
    (realHermite (j+1)).derivative = C ((j : ℝ)+1) * realHermite j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [realHermite_succ (j+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_C_mul]
    calc
      _ = realHermite (j+1) + C ((j : ℝ)+1) * (X*realHermite j - (realHermite j).derivative) := by ring
      _ = _ := by
        rw [← realHermite_succ j]
        push_cast
        simp only [Polynomial.C_add, map_one]
        ring

/-- Polynomial evaluation has a polynomial growth bound given by
the absolute coefficient sum in the power basis. -/
lemma abs_eval_le_coeff_sum (p : ℝ[X]) (x : ℝ) :
    |p.eval x| ≤ (∑ j ∈ p.support, |p.coeff j|)*(1+|x|)^p.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  rw [abs_mul, abs_pow]
  have hDegree := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (abs_nonneg _) (by linarith : |x| ≤ 1+|x|) _).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x]) hDegree)) (abs_nonneg _)

lemma integrable_gaussian_eval (v : ℝ≥0) (p : ℝ[X]) :
    Integrable p.eval (gaussianReal 0 v) :=
  integrable_growth_gaussian v p.natDegree _ (by fun_prop) (abs_eval_le_coeff_sum p)

/-- Integration by parts for evaluating a polynomial against a centered Gaussian. -/
lemma integral_mul_gaussian_eval_eq (v : ℝ≥0) (p : ℝ[X]) :
    (∫ x, x*p.eval x ∂gaussianReal 0 v) =
      (v : ℝ) * ∫ x, p.derivative.eval x ∂gaussianReal 0 v := by
  let r := p.natDegree+p.derivative.natDegree
  let A (q : ℝ[X]) := ∑ j ∈ q.support, |q.coeff j|
  let C := A p + A p.derivative
  have hA (q : ℝ[X]) : 0 ≤ A q := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hGrow (q : ℝ[X]) (h1 : q.natDegree ≤ r) (h2 : A q ≤ C) (x : ℝ) :
      |q.eval x| ≤ C*(1+|x|)^r :=
    (abs_eval_le_coeff_sum q x).trans (mul_le_mul h2
      (pow_le_pow_right₀ (by linarith [abs_nonneg x]) h1) (by positivity) ((hA q).trans h2))
  exact gaussian_integration_by_parts v r C (f := p.eval) (f' := p.derivative.eval)
    p.hasDerivAt (by fun_prop) (hGrow p (Nat.le_add_right ..) (le_add_of_nonneg_right (hA _)))
    (hGrow p.derivative (Nat.le_add_left ..) (le_add_of_nonneg_left (hA _)))

/-- Lowering a Hermite factor in the Gaussian integral differentiates the other factor. -/
theorem integral_realHermite_succ_mul (j : ℕ) (p : ℝ[X]) :
    (∫ x, (realHermite (j+1)).eval x * p.eval x ∂gaussianReal 0 1) =
      ∫ x, (realHermite j).eval x * p.derivative.eval x ∂gaussianReal 0 1 := by
  let H := realHermite j
  have h₀ := integrable_gaussian_eval 1 (X*(H*p))
  have h₁ := integrable_gaussian_eval 1 (H.derivative*p)
  have h₂ := integrable_gaussian_eval 1 (H*p.derivative)
  simp only [eval_mul, eval_X] at h₀ h₁ h₂
  have h := integral_mul_gaussian_eval_eq 1 (H*p)
  simp only [NNReal.coe_one, one_mul, derivative_mul, eval_mul, eval_add] at h
  rw [integral_add h₁ h₂] at h
  rw [realHermite_succ j]
  change (∫ x, (X*H-H.derivative).eval x * p.eval x ∂gaussianReal 0 1) = _
  simp only [eval_sub, eval_mul, eval_X, sub_mul, mul_assoc]
  rw [integral_sub h₀ h₁, h]
  ring

private lemma integral_realHermite_succ_eq_zero (j : ℕ) :
    ∫ x, (realHermite (j+1)).eval x ∂gaussianReal 0 1 = 0 := by
  simpa only [eval_one, mul_one, derivative_one, eval_zero, mul_zero, integral_zero] using
    integral_realHermite_succ_mul j (1 : ℝ[X])

/-- Orthogonality and the factorial squared norm for the unnormalized Hermite polynomials. -/
theorem integral_realHermite_mul (m n : ℕ) :
    (∫ x, (realHermite m).eval x * (realHermite n).eval x ∂gaussianReal 0 1) =
      if m = n then (m.factorial : ℝ) else 0 := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp [Measure.real]
    | succ n => simp [integral_realHermite_succ_eq_zero]
  | succ m ih =>
    cases n with
    | zero => simp [integral_realHermite_succ_eq_zero]
    | succ n =>
      rw [integral_realHermite_succ_mul, derivative_realHermite_succ]
      simp only [eval_mul, eval_C]
      simp_rw [mul_left_comm ((realHermite m).eval _), integral_const_mul, ih]
      by_cases he : m = n
      · subst n
        simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      · simp [he]

/-- The orthonormal probabilists' Hermite function. -/
noncomputable def normalizedHermite (j : ℕ) (x : ℝ) : ℝ :=
  (realHermite j).eval x / Real.sqrt j.factorial

/-- The normalized Hermite functions form an orthonormal family for the standard Gaussian. -/
theorem integral_normalizedHermite_mul (m n : ℕ) :
    (∫ x, normalizedHermite m x * normalizedHermite n x ∂gaussianReal 0 1) =
      if m = n then 1 else 0 := by
  simp_rw [normalizedHermite, ← mul_div_mul_comm, integral_div, integral_realHermite_mul]
  by_cases he : m = n
  · subst n
    simp only [ite_true, Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ m.factorial)]
    exact div_self (by positivity)
  · simp [he]

end LovaszTheta.Circulant
