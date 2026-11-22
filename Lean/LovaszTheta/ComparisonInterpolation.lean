module

public import LovaszTheta.ComparisonFlip
public import LovaszTheta.GaussianInterpolation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Interpolating the sign and Gaussian averages

The scalar Gaussian derivative formula extends by the finite sign
average. The flip identity then separates the derivative into a
covariance term and a Taylor remainder.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal Classical

namespace LovaszTheta.Circulant

/-- Expectation of a test function along the sign-Gaussian interpolation. -/
noncomputable def comparisonMean {Ω : Type*} [Fintype Ω] (v : ℝ≥0)
    (V : Ω → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  average (fun x ↦ ∫ g, f (gaussianBlend t (V x) g) ∂gaussianReal 0 v)

lemma continuousOn_comparisonMean {Ω : Type*} [Fintype Ω] (v : ℝ≥0)
    (V : Ω → ℝ) (C : ℝ) (r : ℕ) (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hf : Continuous f) (hGrow : ∀ x, |f x| ≤ C*(1+|x|)^r) :
    ContinuousOn (comparisonMean v V f) (Icc 0 1) := by
  unfold comparisonMean average
  exact (continuousOn_finsetSum univ fun x _ ↦
    continuousOn_integral_gaussianBlend v (V x) C r hC hf hGrow).div_const _

@[simp]
lemma comparisonMean_zero {Ω : Type*} [Fintype Ω] [Nonempty Ω] (v : ℝ≥0)
    (V : Ω → ℝ) (f : ℝ → ℝ) :
    comparisonMean v V f 0 = ∫ g, f g ∂gaussianReal 0 v := by
  simp [comparisonMean, gaussianBlend]

@[simp]
lemma comparisonMean_one {Ω : Type*} [Fintype Ω] (v : ℝ≥0)
    (V : Ω → ℝ) (f : ℝ → ℝ) :
    comparisonMean v V f 1 = average (f ∘ V) := by
  simp [comparisonMean, gaussianBlend, Function.comp_def]

private lemma integral_average {Ω : Type*} [Fintype Ω] (v : ℝ≥0) (F : Ω → ℝ → ℝ)
    (hF : ∀ x, Integrable (F x) (gaussianReal 0 v)) :
    (∫ g, average (fun x ↦ F x g) ∂gaussianReal 0 v) =
      average (fun x ↦ ∫ g, F x g ∂gaussianReal 0 v) := by
  simp only [average, integral_div, integral_finsetSum _ fun x _ ↦ hF x]

lemma integrable_gaussianBlend {f : ℝ → ℝ} (hf : Continuous f) {r : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hGrow : ∀ x, |f x| ≤ C*(1+|x|)^r) (v : ℝ≥0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    Integrable (fun g ↦ f (gaussianBlend t y g)) (gaussianReal 0 v) := by
  refine integrable_growth_gaussian v r (C*(1+|y|)^r)
    (hf.comp (by unfold gaussianBlend; fun_prop)) ?_
  intro g
  calc
    _ ≤ C*(1+|gaussianBlend t y g|)^r := hGrow _
    _ ≤ C*((1+|y|)*(1+|g|))^r := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (one_add_abs_gaussianBlend_le ht y g) _) hC
    _ = _ := by rw [mul_pow, mul_assoc]

/-- Differentiating the finite average and swapping the sign
and Gaussian integrations. -/
theorem hasDerivAt_comparisonMean {Ω : Type*} [Fintype Ω] (v : ℝ≥0) (V : Ω → ℝ)
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    (hCont : Continuous f'')
    (hf : ∀ x, |f x| ≤ C*(1+|x|)^r)
    (hf' : ∀ x, |f' x| ≤ C*(1+|x|)^r)
    (hf'' : ∀ x, |f'' x| ≤ C*(1+|x|)^r) :
    HasDerivAt (comparisonMean v V f)
      ((1/(2*Real.sqrt t)) * (∫ g, average (fun x ↦ V x * f' (gaussianBlend t (V x) g))
        ∂gaussianReal 0 v) -
        ((v : ℝ)/2) * (∫ g, average (fun x ↦ f'' (gaussianBlend t (V x) g))
          ∂gaussianReal 0 v)) t := by
  have hCont' : Continuous f' := continuous_iff_continuousAt.mpr fun x ↦ (hd' x).continuousAt
  have h₁ (x : Ω) := (integrable_gaussianBlend hCont' hC hf' v (Ioo_subset_Icc_self ht) (V x)).const_mul (V x)
  have h₂ (x : Ω) := integrable_gaussianBlend hCont hC hf'' v (Ioo_subset_Icc_self ht) (V x)
  rw [integral_average v _ h₁, integral_average v _ h₂]
  simp_rw [integral_const_mul, ← average_mul_left, ← average_sub]
  have h (x : Ω) :
      (1/(2*Real.sqrt t)) * (V x * (∫ g, f' (gaussianBlend t (V x) g) ∂gaussianReal 0 v)) =
        (V x/(2*Real.sqrt t)) * (∫ g, f' (gaussianBlend t (V x) g) ∂gaussianReal 0 v) := by ring
  simp_rw [h]
  exact (HasDerivAt.fun_sum (u := (univ : Finset Ω)) fun x _ ↦
    hasDerivAt_integral_gaussianBlend v (V x) C r hC ht hd hd' hCont hf hf' hf'').div_const _

private lemma integrable_average {Ω : Type*} [Fintype Ω] (v : ℝ≥0) (F : Ω → ℝ → ℝ)
    (h : ∀ x, Integrable (F x) (gaussianReal 0 v)) :
    Integrable (fun g ↦ average (fun x ↦ F x g)) (gaussianReal 0 v) := by
  unfold average
  exact (integrable_finsetSum univ fun x _ ↦ h x).div_const _

/-- The derivative as one Gaussian integral, with the sign average
inside so that the exchangeable-pair identity can be applied there. -/
theorem hasDerivAt_comparisonMean_integral {Ω : Type*} [Fintype Ω] (v : ℝ≥0) (V : Ω → ℝ)
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    (hCont : Continuous f'')
    (hf : ∀ x, |f x| ≤ C*(1+|x|)^r)
    (hf' : ∀ x, |f' x| ≤ C*(1+|x|)^r)
    (hf'' : ∀ x, |f'' x| ≤ C*(1+|x|)^r) :
    HasDerivAt (comparisonMean v V f)
      (∫ g, (1/(2*Real.sqrt t)) * average (fun x ↦ V x * f' (gaussianBlend t (V x) g)) -
        ((v : ℝ)/2) * average (fun x ↦ f'' (gaussianBlend t (V x) g)) ∂gaussianReal 0 v) t := by
  have hCont' : Continuous f' := continuous_iff_continuousAt.mpr fun x ↦ (hd' x).continuousAt
  have h₁ (x : Ω) := (integrable_gaussianBlend hCont' hC hf' v (Ioo_subset_Icc_self ht) (V x)).const_mul (V x)
  have h₂ (x : Ω) := integrable_gaussianBlend hCont hC hf'' v (Ioo_subset_Icc_self ht) (V x)
  rw [integral_sub ((integrable_average v _ h₁).const_mul _) ((integrable_average v _ h₂).const_mul _),
    integral_const_mul, integral_const_mul]
  exact hasDerivAt_comparisonMean v V C r hC ht hd hd' hCont hf hf' hf''

/-- An estimate on the interpolation derivative transfers to
the difference of the endpoint expectations. -/
theorem abs_comparisonMean_sub_le_of_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (v : ℝ≥0) (V : Ω → ℝ) (f : ℝ → ℝ) (R : ℝ) (F' : ℝ → ℝ)
    (hCont : ContinuousOn (comparisonMean v V f) (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (comparisonMean v V f) (F' t) t)
    (hBound : ∀ t ∈ Ioo (0 : ℝ) 1, |F' t| ≤ R) :
    |average (f ∘ V) - ∫ g, f g ∂gaussianReal 0 v| ≤ R := by
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (comparisonMean v V f) F' zero_lt_one hCont hd
  simpa only [he, sub_zero, div_one, comparisonMean_one, comparisonMean_zero] using hBound t ht

end LovaszTheta.Circulant
