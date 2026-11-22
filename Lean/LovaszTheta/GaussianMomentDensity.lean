module

public import LovaszTheta.HermiteL2
public import LovaszTheta.MomentUniqueness

/-!
# Vanishing power moments in Gaussian L²

The measures with densities the positive and negative parts of the
function have the same power moments and all exponential moments.
Equality of these measures forces the function to vanish almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LovaszTheta.Circulant

private noncomputable def positiveDensity (f : ℝ → ℝ) : Measure ℝ :=
  (gaussianReal 0 1).withDensity fun x ↦ ENNReal.ofReal (f x)

private noncomputable def positivePart (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (ENNReal.ofReal (f x)).toReal

private lemma positivePart_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ positivePart f x :=
  ENNReal.toReal_nonneg

private lemma memLp_positivePart {f : ℝ → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (gaussianReal 0 1)) : MemLp (positivePart f) 2 (gaussianReal 0 1) := by
  have ha : Measurable (positivePart f) := hm.ennreal_ofReal.ennreal_toReal
  apply hf.norm.mono' ha.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (positivePart_nonneg f x),
      positivePart, ENNReal.toReal_ofReal']
    exact max_le (le_abs_self _) (abs_nonneg _)

private lemma finite_positiveDensity {f : ℝ → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (gaussianReal 0 1)) : IsFiniteMeasure (positiveDensity f) := by
  apply isFiniteMeasure_withDensity
  have hi := (memLp_positivePart hm hf).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he (x : ℝ) : ENNReal.ofReal (f x) = ENNReal.ofReal (positivePart f x) := by
    simp only [positivePart, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (positivePart_nonneg f))]
  exact ENNReal.ofReal_ne_top

private lemma memLp_exp_gaussian (t : ℝ) :
    MemLp (fun x : ℝ ↦ Real.exp (t*x)) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have he (x : ℝ) : Real.exp (t*x)^2 = Real.exp ((2*t)*x) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_mul_gaussianReal (2*t)

private lemma integrableExpSet_positiveDensity {f : ℝ → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (gaussianReal 0 1)) : integrableExpSet id (positiveDensity f) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  change Integrable (fun x ↦ Real.exp (t*x)) (positiveDensity f)
  apply (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  simp only [smul_eq_mul]
  exact (memLp_positivePart hm hf).integrable_mul (memLp_exp_gaussian t)

private lemma integral_pow_positiveDensity {f : ℝ → ℝ} (hm : Measurable f) (j : ℕ) :
    (∫ x, x^j ∂positiveDensity f) = ∫ x, positivePart f x * x^j ∂gaussianReal 0 1 := by
  simpa only [smul_eq_mul, positiveDensity, positivePart] using integral_withDensity_eq_integral_toReal_smul
    (g := fun x : ℝ ↦ x^j) (μ := gaussianReal 0 1) hm.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)

private lemma positivePart_sub_negativePart (f : ℝ → ℝ) (x : ℝ) :
    positivePart f x - positivePart (fun y ↦ -f y) x = f x := by
  simp only [positivePart, ENNReal.toReal_ofReal']
  rcases le_total 0 (f x) with h | h
  · simp only [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · simp only [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- A square integrable function with vanishing power moments is zero
almost everywhere under the standard Gaussian. -/
theorem ae_eq_zero_of_gaussian_power_moments {f : ℝ → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (gaussianReal 0 1))
    (h : ∀ j : ℕ, (∫ x, f x*x^j ∂gaussianReal 0 1) = 0) :
    f =ᵐ[gaussianReal 0 1] 0 := by
  let g (x : ℝ) := -f x
  have hg : Measurable g := hm.neg
  have hgLp : MemLp g 2 (gaussianReal 0 1) := hf.neg
  let _ : IsFiniteMeasure (positiveDensity f) := finite_positiveDensity hm hf
  let _ : IsFiniteMeasure (positiveDensity g) := finite_positiveDensity hg hgLp
  have hMom (j : ℕ) : (∫ x, x^j ∂positiveDensity f) = ∫ x, x^j ∂positiveDensity g := by
    rw [integral_pow_positiveDensity hm, integral_pow_positiveDensity hg, ← sub_eq_zero]
    have hI : Integrable (fun x ↦ positivePart f x * x^j) (gaussianReal 0 1) :=
      (memLp_positivePart hm hf).integrable_mul (memLp_gaussian_pow_two 1 j)
    have hJ : Integrable (fun x ↦ positivePart g x * x^j) (gaussianReal 0 1) :=
      (memLp_positivePart hg hgLp).integrable_mul (memLp_gaussian_pow_two 1 j)
    rw [← integral_sub hI hJ]
    simp_rw [← sub_mul, g, positivePart_sub_negativePart]
    exact h j
  have hEq := measure_eq_of_exponential_moments (integrableExpSet_positiveDensity hm hf)
    (integrableExpSet_positiveDensity hg hgLp) hMom
  have h₁ := Measure.rnDeriv_withDensity (gaussianReal 0 1) hm.ennreal_ofReal
  have h₂ := Measure.rnDeriv_withDensity (gaussianReal 0 1) hg.ennreal_ofReal
  change (positiveDensity f).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1] _ at h₁
  change (positiveDensity g).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1] _ at h₂
  rw [hEq] at h₁
  filter_upwards [h₁.symm.trans h₂] with x hx
  have hp : positivePart f x = positivePart g x := congrArg ENNReal.toReal hx
  have he := positivePart_sub_negativePart f x
  rw [show positivePart (fun y ↦ -f y) x = positivePart g x from rfl, hp, sub_self] at he
  exact he.symm

end LovaszTheta.Circulant
