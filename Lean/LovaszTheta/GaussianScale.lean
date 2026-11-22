module

public import LovaszTheta.Activation
public import LovaszTheta.GaussianAbsoluteMean
public import LovaszTheta.GaussianMomentBounds
public import Mathlib.Analysis.Convex.Integral

/-!
# Choosing the Gaussian scale

The mean of the activation is a continuous, strictly increasing
function of the nonnegative Gaussian scale. Jensen's inequalities
give the variance bounds for the scale solving the manuscript equation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace LovaszTheta.Circulant

/-- Mean activation of a centered Gaussian with scale σ. -/
noncomputable def activationMean (τ σ : ℝ) : ℝ :=
  ∫ g, activation τ (σ*g) ∂gaussianReal 0 1

lemma activationMean_zero (τ : ℝ) : activationMean τ 0 = 2*Real.sqrt τ := by
  simp [activationMean, activation_zero, Measure.real]

lemma abs_activationMean_sub_le {τ : ℝ} (hτ : 0 < τ) (σ s : ℝ) :
    |activationMean τ σ-activationMean τ s| ≤ |σ-s| * (∫ g, |g| ∂gaussianReal 0 1) := by
  let f (g : ℝ) := activation τ (σ*g)
  let u (g : ℝ) := activation τ (s*g)
  have hf := integrable_activation_gaussian 1 hτ.le σ
  have hu := integrable_activation_gaussian 1 hτ.le s
  unfold activationMean
  rw [← integral_sub hf hu]
  refine abs_integral_le_integral_abs.trans ?_
  have hPt (x : ℝ) : |f x-u x| ≤ |σ-s| * |x| := by
    simpa only [f, u, ← sub_mul, abs_mul] using abs_activation_sub_le hτ (σ*x) (s*x)
  exact (integral_mono (hf.sub hu).abs ((integrable_abs_gaussian 1).const_mul |σ-s|) hPt).trans_eq
    (integral_const_mul _ _)

lemma continuous_activationMean {τ : ℝ} (hτ : 0 < τ) : Continuous (activationMean τ) := by
  let c := ∫ g, |g| ∂gaussianReal 0 1
  have hc : 0 ≤ c := integral_nonneg fun _ ↦ abs_nonneg _
  have h : LipschitzWith c.toNNReal (activationMean τ) := by
    apply LipschitzWith.of_dist_le_mul
    intro σ s
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hc, mul_comm c]
    exact abs_activationMean_sub_le hτ σ s
  exact h.continuous

/-- Strict monotonicity of the activation mean in the nonnegative scale. -/
lemma strictMonoOn_activationMean (τ : ℝ) (hτ : 0 ≤ τ) :
    StrictMonoOn (activationMean τ) (Ici 0) := by
  intro σ hσ s hs hsσ
  let _ : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  let f (g : ℝ) := activation τ (s*g)-activation τ (σ*g)
  have hC : Continuous f := by unfold f; exact
    ((continuous_activation τ).comp (by fun_prop)).sub ((continuous_activation τ).comp (by fun_prop))
  have hI : Integrable f (gaussianReal 0 1) :=
    (integrable_activation_gaussian 1 hτ s).sub (integrable_activation_gaussian 1 hτ σ)
  have hNonneg (g : ℝ) : 0 ≤ f g := by
    apply sub_nonneg.mpr
    unfold activation
    apply Real.sqrt_le_sqrt
    rw [mul_pow, mul_pow]
    exact add_le_add_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hσ hsσ.le 2) (sq_nonneg _)) _
  have hAtOne : f 1 ≠ 0 := by
    apply ne_of_gt
    change 0 < activation τ (s*1)-activation τ (σ*1)
    rw [sub_pos, mul_one, mul_one, activation, activation]
    exact Real.sqrt_lt_sqrt (by positivity)
      (add_lt_add_left (pow_lt_pow_left₀ hsσ hσ (by decide : (2 : ℕ) ≠ 0)) _)
  have hp := integral_pos_of_integrable_nonneg_ne_zero hC hI hNonneg hAtOne
  unfold f at hp
  rwa [integral_sub (integrable_activation_gaussian 1 hτ s)
    (integrable_activation_gaussian 1 hτ σ), sub_pos] at hp

lemma integral_sq_standardGaussian :
    (∫ g : ℝ, g^2 ∂gaussianReal 0 1) = 1 := by
  simpa [Measure.real] using integral_pow_gaussian_succ 1 0

lemma integrable_sq_standardGaussian :
    Integrable (fun g : ℝ ↦ g^2) (gaussianReal 0 1) := by
  refine integrable_growth_gaussian 1 2 1 (by fun_prop) fun g ↦ ?_
  rw [one_mul, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _

private lemma convexOn_sq : ConvexOn ℝ (univ : Set ℝ) (fun x : ℝ ↦ x^2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  apply sub_nonneg.mp
  calc
    0 ≤ a*b*(x-y)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    _ = (a+b)*(a*x^2+b*y^2)-(a*x+b*y)^2 := by ring
    _ = _ := by rw [hab, one_mul]

/-- Jensen's inequality for the square gives the lower-variance estimate. -/
lemma activationMean_sq_le {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    activationMean τ σ^2 ≤ σ^2+4*τ := by
  let f (g : ℝ) := activation τ (σ*g)
  have hi (g : ℝ) : f g ^ 2 = σ^2*g^2+4*τ := by
    change activation τ (σ*g)^2 = _
    rw [activation_sq hτ, mul_pow]
  have hσ := integrable_sq_standardGaussian.const_mul (σ^2)
  have hτi : Integrable (fun _ : ℝ ↦ 4*τ) (gaussianReal 0 1) := integrable_const _
  have he : Integrable (fun g ↦ f g ^ 2) (gaussianReal 0 1) := by
    simp_rw [hi]
    exact hσ.add hτi
  have hC : ContinuousOn (fun x : ℝ ↦ x^2) univ := (by fun_prop : Continuous (fun x : ℝ ↦ x^2)).continuousOn
  have hv := convexOn_sq.map_integral_le hC isClosed_univ (ae_of_all _ fun _ ↦ mem_univ _)
    (integrable_activation_gaussian 1 hτ σ) he
  change activationMean τ σ^2 ≤ ∫ x, f x^2 ∂gaussianReal 0 1 at hv
  simp_rw [hi] at hv
  rw [integral_add hσ hτi, integral_const_mul, integral_sq_standardGaussian] at hv
  simpa [Measure.real] using hv

/-- Jensen's inequality for the Euclidean norm applied to the
absolute Gaussian coordinate and the fixed smoothing coordinate. -/
lemma activation_absMean_le {τ σ : ℝ} (hτ : 0 < τ) :
    activation τ (σ*(∫ g, |g| ∂gaussianReal 0 1)) ≤ activationMean τ σ := by
  let m := ∫ g, |g| ∂gaussianReal 0 1
  let a := σ*m
  let p := activation τ a
  have hp : 0 < p := activation_pos hτ a
  have hC (g : ℝ) : (a*(σ*|g|)+4*τ)/p ≤ activation τ (σ*g) := by
    apply (div_le_iff₀ hp).mpr
    apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0)
      (mul_nonneg (activation_nonneg _ _) hp.le)
    rw [mul_pow, activation_sq hτ.le, activation_sq hτ.le, mul_pow]
    have hEq : (a*(σ*|g|)+4*τ)^2 + 4*τ*(a-σ*|g|)^2 =
        (σ^2*g^2+4*τ)*(a^2+4*τ) := by
      rw [← sq_abs g]
      ring
    nlinarith only [hEq, mul_nonneg (show 0 ≤ 4*τ by positivity) (sq_nonneg (a-σ*|g|))]
  have hi := (integrable_abs_gaussian 1).const_mul (a*σ)
  have hj := ((integrable_abs_gaussian 1).const_mul (a*σ)).add (integrable_const (4*τ))
  have he (g : ℝ) : (a*(σ*|g|)+4*τ)/p = ((a*σ)*|g|+4*τ)/p := by ring
  simp_rw [he] at hC
  have h := integral_mono (hj.div_const p) (integrable_activation_gaussian 1 hτ.le σ) hC
  change (∫ g, ((a*σ)*|g|+4*τ)/p ∂gaussianReal 0 1) ≤ activationMean τ σ at h
  rw [integral_div, integral_add hi (integrable_const _), integral_const_mul] at h
  have hh : ((a*σ)*m+4*τ)/p = p := by
    apply (div_eq_iff hp.ne').mpr
    rw [← pow_two, activation_sq hτ.le]
    unfold a
    ring
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
  change ((a*σ)*m+4*τ)/p ≤ _ at h
  rw [hh] at h
  exact h

/-- A positive scale solves the Gaussian mean equation and has its
variance between four and twice π. -/
theorem exists_gaussian_activation_scale {τ : ℝ} (hτ : 0 < τ) :
    ∃ σ : ℝ, 0 < σ ∧ 4 ≤ σ^2 ∧ σ^2 ≤ 2*Real.pi ∧
      activationMean τ σ = 2*Real.sqrt (1+τ) := by
  let t := Real.sqrt (2*Real.pi)
  have ht : 0 < t := by unfold t; positivity
  have hLow : activationMean τ 0 ≤ 2*Real.sqrt (1+τ) := by
    rw [activationMean_zero]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
  have hHigh : 2*Real.sqrt (1+τ) ≤ activationMean τ t := by
    have h := activation_absMean_le (σ := t) hτ
    rw [integral_abs_standardGaussian] at h
    have he : t*(2/Real.sqrt (2*Real.pi)) = 2 := by
      change t*(2/t) = 2
      field_simp [ht.ne']
    rw [he] at h
    have h₂ : activation τ 2 = 2*Real.sqrt (1+τ) := by
      rw [activation, show (2 : ℝ)^2+4*τ = 4*(1+τ) by ring, Real.sqrt_mul (by norm_num),
        show Real.sqrt (4 : ℝ) = 2 by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]
    simpa only [h₂] using h
  obtain ⟨σ, hσ, hmean⟩ := intermediate_value_Icc ht.le (continuous_activationMean hτ).continuousOn
    (show 2*Real.sqrt (1+τ) ∈ Icc (activationMean τ 0) (activationMean τ t) from ⟨hLow, hHigh⟩)
  have hlo := activationMean_sq_le hτ.le σ
  rw [hmean, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1+τ)] at hlo
  have h4 : 4 ≤ σ^2 := by linarith
  have hpos : 0 < σ := by
    by_contra h
    have hzero : σ = 0 := le_antisymm (le_of_not_gt h) hσ.1
    rw [hzero] at h4
    norm_num at h4
  have hSq : σ^2 ≤ 2*Real.pi := by
    exact (pow_le_pow_left₀ hσ.1 hσ.2 2).trans_eq (Real.sq_sqrt (by positivity))
  exact ⟨σ, hpos, h4, hSq, hmean⟩

end LovaszTheta.Circulant
