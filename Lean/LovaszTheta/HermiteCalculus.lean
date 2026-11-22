module

public import LovaszTheta.HermiteCompleteness

/-!
# Hermite coefficients of a derivative

Polynomial growth is preserved by the products and sums in the
Gaussian integration-by-parts calculation. The normalized lowering
identity gives the coefficient of a derivative.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Polynomial
open scoped Polynomial NNReal ENNReal

namespace LovaszTheta.Circulant

/-- A function bounded in magnitude by a constant times a polynomial in its input magnitude. -/
def HasPolynomialGrowth (f : ℝ → ℝ) : Prop :=
  ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C*(1+|x|)^r

namespace HasPolynomialGrowth

variable {f g : ℝ → ℝ}

private lemma bound_mono {r s : ℕ} {C D : ℝ} (hr : r ≤ s) (hC : C ≤ D) (hD : 0 ≤ D)
    (hf : ∀ x, |f x| ≤ C*(1+|x|)^r) (x : ℝ) : |f x| ≤ D*(1+|x|)^s :=
  (hf x).trans (mul_le_mul hC (pow_le_pow_right₀ (by linarith [abs_nonneg x]) hr) (by positivity) hD)

lemma add (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth (fun x ↦ f x+g x) := by
  obtain ⟨r, C, hC, hf⟩ := hf
  obtain ⟨s, D, hD, hg⟩ := hg
  refine ⟨r+s, C+D, add_nonneg hC hD, fun x ↦ ?_⟩
  rw [add_mul]
  exact (abs_add_le _ _).trans (add_le_add (bound_mono (Nat.le_add_right ..) le_rfl hC hf x)
    (bound_mono (Nat.le_add_left ..) le_rfl hD hg x))

lemma mul (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth (fun x ↦ f x*g x) := by
  obtain ⟨r, C, hC, hf⟩ := hf
  obtain ⟨s, D, hD, hg⟩ := hg
  refine ⟨r+s, C*D, mul_nonneg hC hD, fun x ↦ ?_⟩
  rw [abs_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)

lemma of_bound {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) : HasPolynomialGrowth f :=
  ⟨0, C, hC, fun x ↦ by simpa only [pow_zero, mul_one] using hf x⟩

lemma eval_polynomial (p : ℝ[X]) : HasPolynomialGrowth p.eval :=
  ⟨p.natDegree, ∑ j ∈ p.support, |p.coeff j|, sum_nonneg fun _ _ ↦ abs_nonneg _, abs_eval_le_coeff_sum p⟩

lemma integrable_gaussian (hf : HasPolynomialGrowth f) (hCont : Continuous f) (v : ℝ≥0) :
    Integrable f (gaussianReal 0 v) := by
  obtain ⟨r, C, _, h⟩ := hf
  exact integrable_growth_gaussian v r C hCont h

lemma memLp_gaussian_two (hf : HasPolynomialGrowth f) (hCont : Continuous f) (v : ℝ≥0) :
    MemLp f 2 (gaussianReal 0 v) := by
  rw [memLp_two_iff_integrable_sq hCont.aestronglyMeasurable]
  simpa only [pow_two] using (hf.mul hf).integrable_gaussian (hCont.mul hCont) v

/-- Integration by parts when the function and derivative have possibly different growth orders. -/
lemma gaussian_integration_by_parts (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g)
    (hd : ∀ x, HasDerivAt f (g x) x) (hCont : Continuous g) (v : ℝ≥0) :
    (∫ x, x*f x ∂gaussianReal 0 v) = (v : ℝ)*∫ x, g x ∂gaussianReal 0 v := by
  obtain ⟨r, C, hC, hf⟩ := hf
  obtain ⟨s, D, hD, hg⟩ := hg
  exact LovaszTheta.Circulant.gaussian_integration_by_parts v (r+s) (C+D) hd hCont
    (bound_mono (Nat.le_add_right ..) (le_add_of_nonneg_right hD) (add_nonneg hC hD) hf)
    (bound_mono (Nat.le_add_left ..) (le_add_of_nonneg_left hC) (add_nonneg hC hD) hg)

end HasPolynomialGrowth

/-- Gaussian integration by parts with a Hermite factor and a test function. -/
theorem integral_realHermite_succ_mul_of_growth (j : ℕ) {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hCont' : Continuous f')
    (hf : HasPolynomialGrowth f) (hf' : HasPolynomialGrowth f') :
    (∫ x, f x*(realHermite (j+1)).eval x ∂gaussianReal 0 1) =
      ∫ x, f' x*(realHermite j).eval x ∂gaussianReal 0 1 := by
  let H := realHermite j
  have hCont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hd x).continuousAt
  have hH : Continuous H.eval := by fun_prop
  have hHd : Continuous H.derivative.eval := by fun_prop
  have hG : HasPolynomialGrowth H.eval := HasPolynomialGrowth.eval_polynomial H
  have hG' : HasPolynomialGrowth H.derivative.eval := HasPolynomialGrowth.eval_polynomial H.derivative
  have hIbp := (hG.mul hf).gaussian_integration_by_parts ((hG'.mul hf).add (hG.mul hf'))
    (fun x ↦ by
      have h := (H.hasDerivAt x).mul (hd x)
      change HasDerivAt (fun x ↦ H.eval x*f x)
        (H.derivative.eval x*f x+H.eval x*f' x) x at h
      exact h)
    ((hHd.mul hCont).add (hH.mul hCont')) 1
  have h₁ := (hG'.mul hf).integrable_gaussian (hHd.mul hCont) 1
  have h₂ := (hG.mul hf').integrable_gaussian (hH.mul hCont') 1
  have h₀ := ((HasPolynomialGrowth.eval_polynomial (X : ℝ[X])).mul (hG.mul hf)).integrable_gaussian
    ((by fun_prop : Continuous (X : ℝ[X]).eval).mul (hH.mul hCont)) 1
  simp only [eval_X] at h₀
  rw [NNReal.coe_one, one_mul, integral_add h₁ h₂] at hIbp
  have he (x : ℝ) : f x*(realHermite (j+1)).eval x = x*(H.eval x*f x)-H.derivative.eval x*f x := by
    rw [realHermite_succ j]
    simp only [eval_sub, eval_mul, eval_X]
    unfold H
    ring
  simp_rw [he]
  rw [integral_sub h₀ h₁, hIbp, add_sub_cancel_left]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ mul_comm _ _)

/-- Differentiation shifts the coefficients by one and multiplies by
the square root of the original index. -/
theorem hermiteCoefficient_derivative (j : ℕ) {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hCont' : Continuous f')
    (hf : HasPolynomialGrowth f) (hf' : HasPolynomialGrowth f') :
    hermiteCoefficient f' j = Real.sqrt ((j : ℝ)+1) * hermiteCoefficient f (j+1) := by
  simp_rw [hermiteCoefficient, normalizedHermite, ← mul_div_assoc, integral_div]
  rw [integral_realHermite_succ_mul_of_growth j hd hCont' hf hf',
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Real.sqrt_mul (by positivity)]
  have h₁ : Real.sqrt ((j : ℝ)+1) ≠ 0 := by positivity
  have h₂ : Real.sqrt (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp [h₁, h₂]

end LovaszTheta.Circulant
