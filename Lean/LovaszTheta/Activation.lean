module

public import LovaszTheta.GaussianIntegration
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The smoothed absolute value in the Gaussian equation

The activation is even and smooth for a positive smoothing parameter.
Its derivative is strictly smaller than one in magnitude.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LovaszTheta.Circulant

/-- The scalar activation in the Gaussian equation. -/
noncomputable def activation (τ x : ℝ) : ℝ := Real.sqrt (x^2+4*τ)

lemma activation_nonneg (τ x : ℝ) : 0 ≤ activation τ x := Real.sqrt_nonneg _

lemma activation_pos {τ : ℝ} (hτ : 0 < τ) (x : ℝ) : 0 < activation τ x :=
  Real.sqrt_pos.mpr (by positivity)

lemma activation_even (τ : ℝ) : (activation τ).Even := by
  intro x
  simp [activation]

lemma activation_sq {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    activation τ x ^ 2 = x^2+4*τ :=
  Real.sq_sqrt (by positivity)

lemma abs_le_activation {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : |x| ≤ activation τ x := by
  rw [activation, ← Real.sqrt_sq_eq_abs x]
  apply Real.sqrt_le_sqrt
  linarith

lemma activation_le_abs_add {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    activation τ x ≤ |x|+2*Real.sqrt τ := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith only [Real.sq_sqrt hτ, sq_abs x, mul_nonneg (abs_nonneg x) (Real.sqrt_nonneg τ)]

lemma activation_zero (τ : ℝ) : activation τ 0 = 2*Real.sqrt τ := by
  rw [activation, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
  rw [show Real.sqrt (4 : ℝ) = 2 by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]

lemma continuous_activation (τ : ℝ) : Continuous (activation τ) := by
  unfold activation
  fun_prop

theorem hasDerivAt_activation {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    HasDerivAt (activation τ) (x / activation τ x) x := by
  have hp : HasDerivAt (fun y : ℝ ↦ y^2+4*τ) (2*x) x := by
    convert (hasDerivAt_pow 2 x).add_const (4*τ) using 1
    norm_num
  have hPos : x^2+4*τ ≠ 0 := by positivity
  convert hp.sqrt hPos using 1
  · rfl
  · exact (mul_div_mul_left x (activation τ x) two_ne_zero).symm

theorem contDiff_activation {τ : ℝ} (hτ : 0 < τ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (activation τ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hP : ContDiffAt ℝ r (fun y : ℝ ↦ y^2+4*τ) x := by fun_prop
  exact (Real.contDiffAt_sqrt (by positivity : x^2+4*τ ≠ 0)).comp x hP

lemma abs_activation_derivative_lt_one {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    |x/activation τ x| < 1 := by
  have hPos := activation_pos hτ x
  rw [abs_div, abs_of_pos hPos, div_lt_iff₀ hPos, one_mul, activation]
  apply (Real.lt_sqrt (abs_nonneg x)).mpr
  rw [sq_abs]
  linarith

/-- The Lipschitz estimate used when transferring the truncated Gaussian combination. -/
theorem abs_activation_sub_le {τ : ℝ} (hτ : 0 < τ) (x y : ℝ) :
    |activation τ x-activation τ y| ≤ |x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := y) (y := x)
    (fun u _ ↦ (hasDerivAt_activation hτ u).hasDerivWithinAt)
    (fun u _ ↦ by simpa only [Real.norm_eq_abs] using (abs_activation_derivative_lt_one hτ u).le)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs, one_mul] using h

lemma integrable_activation_gaussian (v : ℝ≥0) {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    Integrable (fun g ↦ activation τ (σ*g)) (gaussianReal 0 v) := by
  apply integrable_growth_gaussian v 1 (|σ|+2*Real.sqrt τ)
    ((continuous_activation τ).comp (by fun_prop))
  intro x
  change |activation τ (σ*x)| ≤ _
  rw [abs_of_nonneg (activation_nonneg _ _), pow_one]
  refine (activation_le_abs_add hτ (σ*x)).trans ?_
  rw [abs_mul]
  nlinarith only [abs_nonneg σ, mul_nonneg (Real.sqrt_nonneg τ) (abs_nonneg x)]

end LovaszTheta.Circulant
