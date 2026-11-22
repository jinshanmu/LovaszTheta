module

public import LovaszTheta.GaussianSeriesMoments

/-!
# Normalized finite truncations

A unit coefficient vector is the limit of its finite
truncations normalized to unit norm. The finite variance is
the finite sum of the squared coefficients.
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped Classical ENNReal Topology

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- Keep only the indicated coefficients of a square-summable vector. -/
noncomputable def truncateCoefficients (a : lp (fun _ : I ↦ ℝ) 2) (s : Finset I) :
    lp (fun _ : I ↦ ℝ) 2 :=
  ∑ i ∈ s, lp.single 2 i (a i)

lemma truncateCoefficients_apply (a : lp (fun _ : I ↦ ℝ) 2) (s : Finset I) (i : I) :
    truncateCoefficients a s i = if i ∈ s then a i else 0 := by
  rw [truncateCoefficients, lp.coeFn_sum]
  change (∑ j ∈ s, (fun k ↦ lp.single 2 j (a j) k)) i = _
  simp [Finset.sum_apply,lp.single_apply,Pi.single_apply]

lemma truncateCoefficients_eq_self {a : lp (fun _ : I ↦ ℝ) 2} {s : Finset I}
    (ha : ∀ i ∉ s, a i = 0) : truncateCoefficients a s = a := by
  ext i
  rw [truncateCoefficients_apply]
  by_cases hi : i ∈ s <;> simp [hi, ha]

lemma hasSum_gaussianCoefficient_norm_sq (a : lp (fun _ : I ↦ ℝ) 2) :
    HasSum (fun i ↦ (a i)^2) (‖a‖^2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using h

lemma sum_sq_eq_gaussianCoefficient_norm_sq {a : lp (fun _ : I ↦ ℝ) 2} {s : Finset I}
    (ha : ∀ i ∉ s, a i = 0) : (∑ i ∈ s, (a i)^2) = ‖a‖^2 := by
  rw [← (hasSum_gaussianCoefficient_norm_sq a).tsum_eq]
  exact (tsum_eq_sum (fun i hi ↦ by rw [ha i hi,zero_pow (by decide)])).symm

/-- Normalize a finite truncation to have variance one when it is nonzero. -/
noncomputable def normalizedTruncation (a : lp (fun _ : I ↦ ℝ) 2) (s : Finset I) :
    lp (fun _ : I ↦ ℝ) 2 :=
  ‖truncateCoefficients a s‖⁻¹ • truncateCoefficients a s

lemma normalizedTruncation_apply_of_notMem (a : lp (fun _ : I ↦ ℝ) 2) (s : Finset I)
    (i : I) (hi : i ∉ s) : normalizedTruncation a s i = 0 := by
  simp [normalizedTruncation,lp.coeFn_smul,truncateCoefficients_apply,hi]

lemma tendsto_normalizedTruncation (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    Tendsto (normalizedTruncation a) atTop (𝓝 a) := by
  have h : Tendsto (truncateCoefficients a) atTop (𝓝 a) := lp.hasSum_single (by norm_num) a
  have hN : Tendsto (fun s ↦ ‖truncateCoefficients a s‖) atTop (𝓝 1) := ha ▸ h.norm
  change Tendsto (fun s ↦ ‖truncateCoefficients a s‖⁻¹ • truncateCoefficients a s) atTop (𝓝 a)
  simpa only [inv_one,one_smul] using (hN.inv₀ one_ne_zero).smul h

lemma eventually_normalizedTruncation_norm_one (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    ∀ᶠ s : Finset I in atTop, ‖normalizedTruncation a s‖ = 1 := by
  have h : Tendsto (truncateCoefficients a) atTop (𝓝 a) := lp.hasSum_single (by norm_num) a
  have hN : Tendsto (fun s ↦ ‖truncateCoefficients a s‖) atTop (𝓝 1) := ha ▸ h.norm
  filter_upwards [hN.eventually (lt_mem_nhds zero_lt_one)] with s hs
  rw [normalizedTruncation,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel₀ hs.ne']

end LovaszTheta.Circulant
