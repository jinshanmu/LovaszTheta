module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

Polynomial growth ensures integrability under a real Gaussian law.
Applied to the density times a test function, the fundamental theorem
of calculus on the real line gives the Gaussian integration rule.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LovaszTheta.Circulant

lemma integrable_growth_gaussian (v : ℝ≥0) (r : ℕ) (C : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (h : ∀ x, |f x| ≤ C * (1 + |x|)^r) :
    Integrable f (gaussianReal 0 v) := by
  have hp : MemLp (fun x : ℝ ↦ 1 + |x|) (r : ℝ≥0∞) (gaussianReal 0 v) := by
    have hId := (memLp_id_gaussianReal (μ := 0) (v := v) (r : ℝ≥0)).norm
    simpa only [Real.norm_eq_abs, id_eq, ENNReal.coe_natCast, Pi.add_def] using
      (memLp_const (1 : ℝ)).add hId
  have hi := hp.integrable_norm_pow'.const_mul C
  apply hi.mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |x|)] using h x

private lemma integrable_density_mul {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 v)) :
    Integrable (fun x ↦ gaussianPDFReal 0 v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)).mp hf

/-- Derivative of the centered Gaussian density. -/
lemma hasDerivAt_centered_gaussianPDFReal (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  simp only [gaussianPDFReal_def, sub_zero]
  have hSquare : HasDerivAt (fun y : ℝ ↦ y^2) (2*x) x := by
    convert (hasDerivAt_id' x).pow 2 using 1
    norm_num
  have hExponent : HasDerivAt (fun y : ℝ ↦ -(y^2) / (2 * (v : ℝ))) (-(x / (v : ℝ))) x := by
    convert hSquare.neg.div_const (2 * (v : ℝ)) using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  convert hExponent.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹ using 1
  ring

/-- Gaussian integration by parts for a differentiable test function
whose value and derivative have polynomial growth. -/
theorem gaussian_integration_by_parts (v : ℝ≥0) (r : ℕ) (C : ℝ) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hf : ∀ x, |f x| ≤ C * (1 + |x|)^r) (hg : ∀ x, |f' x| ≤ C * (1 + |x|)^r) :
    (∫ x, x * f x ∂gaussianReal 0 v) = (v : ℝ) * ∫ x, f' x ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · simp [hv]
  have hCont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hderiv x).continuousAt
  have hi := integrable_density_mul hv (integrable_growth_gaussian v r C hCont hf)
  have hdi := integrable_density_mul hv (integrable_growth_gaussian v r C hf' hg)
  have hxf : ∀ x, |x * f x| ≤ C * (1 + |x|)^(r+1) := by
    intro x
    rw [abs_mul, pow_succ, ← mul_assoc]
    calc
      _ ≤ |x| * (C * (1 + |x|)^r) := mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
      _ = (C * (1 + |x|)^r) * |x| := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ((abs_nonneg (f x)).trans (hf x))
  have hxi := integrable_density_mul hv (integrable_growth_gaussian v (r+1) C
    (by fun_prop : Continuous fun x ↦ x * f x) hxf)
  let w := gaussianPDFReal 0 v
  have hd (x : ℝ) : HasDerivAt (fun y ↦ w y * f y)
      (w x * f' x - (v : ℝ)⁻¹ * (w x * (x * f x))) x := by
    convert (hasDerivAt_centered_gaussianPDFReal v x).mul (hderiv x) using 1
    ring
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hd (hdi.sub (hxi.const_mul _)) hi
  rw [integral_sub hdi (hxi.const_mul _), integral_const_mul] at h
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  change (∫ x, w x * (x * f x)) = (v : ℝ) * ∫ x, w x * f' x
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  rw [sub_eq_zero] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hvR, one_mul]

end LovaszTheta.Circulant
