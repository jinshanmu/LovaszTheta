module

public import LovaszTheta.GaussianScale
public import LovaszTheta.HermiteCalculus
public import LovaszTheta.HermiteParity

/-!
# Energy of the activation's Hermite expansion

Parseval and the Gaussian mean equation give the mass in positive
degrees. Integration by parts gives its degree-weighted energy
and makes the resulting offspring law subcritical.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace LovaszTheta.Circulant

/-- Hermite coefficients of the activation of a scaled standard normal. -/
noncomputable def activationCoefficient (τ σ : ℝ) (j : ℕ) : ℝ :=
  hermiteCoefficient (fun g ↦ activation τ (σ*g)) j

@[simp]
lemma activationCoefficient_zero (τ σ : ℝ) : activationCoefficient τ σ 0 = activationMean τ σ := by
  rw [activationCoefficient, hermiteCoefficient_zero]
  rfl

lemma continuous_scaled_activation (τ σ : ℝ) : Continuous (fun g ↦ activation τ (σ*g)) :=
  (continuous_activation τ).comp (by fun_prop)

lemma hasPolynomialGrowth_scaled_activation {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    HasPolynomialGrowth (fun g ↦ activation τ (σ*g)) := by
  refine ⟨1, |σ|+2*Real.sqrt τ, by positivity, fun x ↦ ?_⟩
  rw [abs_of_nonneg (activation_nonneg _ _), pow_one]
  refine (activation_le_abs_add hτ (σ*x)).trans ?_
  rw [abs_mul]
  nlinarith only [abs_nonneg σ, mul_nonneg (Real.sqrt_nonneg τ) (abs_nonneg x)]

lemma activationCoefficient_eq_zero_of_odd (τ σ : ℝ) {j : ℕ} (hj : Odd j) :
    activationCoefficient τ σ j = 0 := by
  apply hermiteCoefficient_eq_zero_of_odd_of_even (continuous_scaled_activation τ σ) _ hj
  intro x
  change activation τ (σ*(-x)) = activation τ (σ*x)
  rw [mul_neg, activation_even]

private lemma integral_scaled_activation_sq {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    (∫ g, activation τ (σ*g)^2 ∂gaussianReal 0 1) = σ^2+4*τ := by
  have h (x : ℝ) : activation τ (σ*x)^2 = σ^2*x^2+4*τ := by rw [activation_sq hτ, mul_pow]
  simp_rw [h]
  rw [integral_add (integrable_sq_standardGaussian.const_mul _) (integrable_const _),
    integral_const_mul, integral_sq_standardGaussian]
  simp [Measure.real]

lemma hasSum_activationCoefficient_sq {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    HasSum (fun j ↦ activationCoefficient τ σ j^2) (σ^2+4*τ) := by
  have h := hasSum_sq_hermiteCoefficient
    ((hasPolynomialGrowth_scaled_activation hτ σ).memLp_gaussian_two (continuous_scaled_activation τ σ) 1)
  simpa only [activationCoefficient, integral_scaled_activation_sq hτ σ] using h

/-- The constant coefficient accounts for all the mass removed from
the Hermite expansion before the root is grafted. -/
theorem hasSum_activationCoefficient_sq_tail {τ σ : ℝ} (hτ : 0 ≤ τ)
    (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    HasSum (fun j ↦ activationCoefficient τ σ (j+2)^2) (σ^2-4) := by
  have h := (hasSum_nat_add_iff' 2).mpr (hasSum_activationCoefficient_sq hτ σ)
  have h₁ : activationCoefficient τ σ 1 = 0 := activationCoefficient_eq_zero_of_odd τ σ (by decide)
  have he : σ^2+4*τ-(∑ i ∈ range 2, activationCoefficient τ σ i^2) = σ^2-4 := by
    simp only [sum_range_succ, sum_range_zero, zero_add, activationCoefficient_zero, h₁, zero_pow
      (by decide : (2 : ℕ) ≠ 0), add_zero, hMean, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1+τ)]
    ring
  rw [he] at h
  exact h

private noncomputable def scaledActivationDerivative (τ σ x : ℝ) : ℝ :=
  σ*(σ*x/activation τ (σ*x))

private lemma hasDerivAt_scaledActivation {τ : ℝ} (hτ : 0 < τ) (σ x : ℝ) :
    HasDerivAt (fun g ↦ activation τ (σ*g)) (scaledActivationDerivative τ σ x) x := by
  have h := (hasDerivAt_activation hτ (σ*x)).comp x ((hasDerivAt_id' x).const_mul σ)
  simpa only [Function.comp_def, mul_one, scaledActivationDerivative, mul_comm] using h

private lemma continuous_scaledActivationDerivative {τ : ℝ} (hτ : 0 < τ) (σ : ℝ) :
    Continuous (scaledActivationDerivative τ σ) := by
  unfold scaledActivationDerivative
  exact continuous_const.mul ((by fun_prop : Continuous (fun x : ℝ ↦ σ*x)).div
    (continuous_scaled_activation τ σ) (fun x ↦ (activation_pos hτ _).ne'))

private lemma abs_scaledActivationDerivative_le {τ : ℝ} (hτ : 0 < τ) (σ x : ℝ) :
    |scaledActivationDerivative τ σ x| ≤ |σ| := by
  rw [scaledActivationDerivative, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_activation_derivative_lt_one hτ _).le

private lemma growth_scaledActivationDerivative {τ : ℝ} (hτ : 0 < τ) (σ : ℝ) :
    HasPolynomialGrowth (scaledActivationDerivative τ σ) :=
  HasPolynomialGrowth.of_bound (abs_nonneg _) (abs_scaledActivationDerivative_le hτ σ)

private lemma integral_scaledActivationDerivative_sq_lt {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) :
    (∫ x, scaledActivationDerivative τ σ x ^ 2 ∂gaussianReal 0 1) < σ^2 := by
  let _ : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  let d := scaledActivationDerivative τ σ
  let f (x : ℝ) := σ^2-d x^2
  have hd := continuous_scaledActivationDerivative hτ σ
  have hG := growth_scaledActivationDerivative hτ σ
  have hReal : Continuous f := continuous_const.sub (hd.pow _)
  have hi : Integrable (fun x ↦ d x^2) (gaussianReal 0 1) := by
    simpa only [pow_two] using (hG.mul hG).integrable_gaussian (hd.mul hd) 1
  have hf : Integrable f (gaussianReal 0 1) := (integrable_const _).sub hi
  have hPt (x : ℝ) : 0 ≤ f x := by
    apply sub_nonneg.mpr
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_scaledActivationDerivative_le hτ σ x) 2
    simpa only [sq_abs] using h
  have hAtZero : f 0 ≠ 0 := by
    simpa [f, d, scaledActivationDerivative] using (pow_ne_zero 2 hσ.ne')
  have h := integral_pos_of_integrable_nonneg_ne_zero hReal hf hPt hAtZero
  unfold f at h
  rw [integral_sub (integrable_const _) hi, integral_const, sub_pos] at h
  simpa [Measure.real] using h

/-- The Hermite energy equals the derivative's mean square, which
is strictly below the Gaussian variance. -/
theorem activation_hermite_energy {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) :
    ∃ e : ℝ, HasSum (fun j : ℕ ↦ ((j : ℝ)+1)*activationCoefficient τ σ (j+1)^2) e ∧ e < σ^2 := by
  let d := scaledActivationDerivative τ σ
  have hC := continuous_scaledActivationDerivative hτ σ
  have hG := growth_scaledActivationDerivative hτ σ
  have hP := hasSum_sq_hermiteCoefficient (hG.memLp_gaussian_two hC 1)
  have hShift (j : ℕ) : hermiteCoefficient d j =
      Real.sqrt ((j : ℝ)+1)*activationCoefficient τ σ (j+1) :=
    hermiteCoefficient_derivative j (hasDerivAt_scaledActivation hτ σ) hC
      (hasPolynomialGrowth_scaled_activation hτ.le σ) hG
  refine ⟨∫ x, d x^2 ∂gaussianReal 0 1, ?_, integral_scaledActivationDerivative_sq_lt hτ hσ⟩
  have hSq (j : ℕ) : Real.sqrt ((j : ℝ)+1)^2 = (j : ℝ)+1 := Real.sq_sqrt (by positivity)
  change HasSum (fun j ↦ hermiteCoefficient d j ^ 2) (∫ x, d x^2 ∂gaussianReal 0 1) at hP
  simpa only [hShift, mul_pow, hSq] using hP

/-- Offspring probabilities for the Gaussian construction. -/
noncomputable def gaussianOffspringProbability (τ σ : ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 4 else activationCoefficient τ σ j^2) / σ^2

lemma gaussianOffspringProbability_nonneg (τ σ : ℝ) (j : ℕ) :
    0 ≤ gaussianOffspringProbability τ σ j := by
  unfold gaussianOffspringProbability
  split_ifs <;> positivity

lemma gaussianOffspringProbability_eq_zero_of_odd (τ σ : ℝ) {j : ℕ} (hj : Odd j) :
    gaussianOffspringProbability τ σ j = 0 := by
  have hne : j ≠ 0 := fun he ↦ (by decide : ¬Odd (0 : ℕ)) (he ▸ hj)
  simp [gaussianOffspringProbability, hne, activationCoefficient_eq_zero_of_odd τ σ hj]

/-- The offspring law has total mass one and mean strictly below one. -/
theorem gaussianOffspringProbability_mass_and_mean {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    HasSum (gaussianOffspringProbability τ σ) 1 ∧
      ∃ m : ℝ, HasSum (fun j : ℕ ↦ (j : ℝ)*gaussianOffspringProbability τ σ j) m ∧ m < 1 := by
  constructor
  · have h := (hasSum_activationCoefficient_sq_tail hτ.le hMean).div_const (σ^2)
    have hne (j : ℕ) : j+2 ≠ 0 := by omega
    have ht : HasSum (fun j ↦ gaussianOffspringProbability τ σ (j+2)) ((σ^2-4)/σ^2) := by
      simpa only [gaussianOffspringProbability, ite_eq_right (hne _)] using h
    have hs := (hasSum_nat_add_iff 2).mp ht
    have he : ∑ j ∈ range 2, gaussianOffspringProbability τ σ j = 4/σ^2 := by
      simp [sum_range_succ, gaussianOffspringProbability,
        activationCoefficient_eq_zero_of_odd τ σ (by decide : Odd 1)]
    rw [he, ← add_div, sub_add_cancel, div_self (by positivity : σ^2 ≠ 0)] at hs
    exact hs
  · obtain ⟨e, he, hlt⟩ := activation_hermite_energy hτ hσ
    have ht := he.div_const (σ^2)
    have hs : HasSum (fun j ↦ ((j+1 : ℕ) : ℝ) * gaussianOffspringProbability τ σ (j+1)) (e/σ^2) := by
      simpa only [gaussianOffspringProbability, Nat.add_one_ne_zero, ite_false, Nat.cast_add,
        Nat.cast_one, mul_div_assoc] using ht
    have hm := (hasSum_nat_add_iff (f := fun j : ℕ ↦ (j : ℝ)*gaussianOffspringProbability τ σ j) 1).mp hs
    simp only [sum_range_one, Nat.cast_zero, zero_mul, add_zero] at hm
    exact ⟨e/σ^2, hm, (div_lt_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hlt)⟩

end LovaszTheta.Circulant
