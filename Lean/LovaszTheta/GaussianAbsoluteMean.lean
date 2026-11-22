module

public import LovaszTheta.GaussianIntegration

/-!
# Absolute mean of a standard Gaussian

On the positive and negative half-lines the integrand is, up to
sign, the derivative of the unnormalized Gaussian density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace LovaszTheta.Circulant

lemma integrable_abs_gaussian (v : ℝ≥0) : Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 v) :=
  integrable_growth_gaussian v 1 1 (by fun_prop) (fun x ↦ by
    simp only [abs_abs, pow_one, one_mul]
    linarith)

private lemma integral_abs_mul_gaussian_kernel :
    (∫ x : ℝ, |x| *Real.exp (-(1/2 : ℝ)*x^2)) = 2 := by
  let F (x : ℝ) := Real.exp (-(1/2 : ℝ)*x^2)
  have hDer (x : ℝ) : HasDerivAt F (-x * F x) x := by
    have hp : HasDerivAt (fun y : ℝ ↦ -(1/2 : ℝ)*y^2) (-x) x := by
      convert (hasDerivAt_pow 2 x).const_mul (-(1/2 : ℝ)) using 1
      norm_num
      ring
    convert hp.exp using 1
    unfold F
    ring
  have hTop : Tendsto F atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (by norm_num : -(1/2 : ℝ) < 0))
  have hBot : Tendsto F atBot (𝓝 0) := by
    simpa only [Function.comp_def, F, neg_sq] using hTop.comp tendsto_neg_atBot_atTop
  have hI : Integrable (fun x ↦ x*F x) := integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))
  have hN : Integrable (fun x ↦ -x * F x) := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hI.const_mul (-1)
  have hAbs : Integrable (fun x ↦ |x| *F x) := by
    have hPos (x : ℝ) : |F x| = F x := abs_of_nonneg (Real.exp_nonneg _)
    simpa only [abs_mul, hPos] using hI.abs
  have hMinus := integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun x _ ↦ hDer x) hN.integrableOn hBot
  have hPlus := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun x _ ↦ hDer x) hN.integrableOn hTop
  have h₀ : F 0 = 1 := by simp [F]
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hAbs, compl_Ioi]
  have hm : (∫ x in Iic (0 : ℝ), |x| *F x) = 1 := by
    calc
      _ = ∫ x in Iic (0 : ℝ), -x * F x := by
        apply setIntegral_congr_fun measurableSet_Iic
        exact fun x hx ↦ by rw [abs_of_nonpos hx]
      _ = _ := by rw [hMinus, h₀, sub_zero]
  have hp : (∫ x in Ioi (0 : ℝ), |x| *F x) = 1 := by
    have he : (∫ x in Ioi (0 : ℝ), |x| *F x) = -(∫ x in Ioi (0 : ℝ), -x * F x) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change |x| * F x = -(-x * F x)
      rw [abs_of_nonneg hx.le, neg_mul, neg_neg]
    rw [he, hPlus, h₀]
    norm_num
  rw [hp, hm]
  norm_num

/-- The absolute first moment of a standard normal. -/
theorem integral_abs_standardGaussian :
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) = 2 / Real.sqrt (2*Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, smul_eq_mul]
  have h (x : ℝ) : (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(x^2)/2) * |x| =
      (Real.sqrt (2*Real.pi))⁻¹ * (|x| * Real.exp (-(1/2 : ℝ)*x^2)) := by
    rw [show -(x^2)/2 = -(1/2 : ℝ)*x^2 by ring]
    ring
  simp_rw [h, integral_const_mul, integral_abs_mul_gaussian_kernel]
  ring

end LovaszTheta.Circulant
