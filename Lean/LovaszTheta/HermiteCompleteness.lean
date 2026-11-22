module

public import LovaszTheta.GaussianMomentDensity

/-!
# Completeness and Parseval for the Hermite functions

The orthogonal complement of their span consists of functions whose
power moments vanish. This gives the Gaussian Hermite Hilbert basis
and the squared-coefficient identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Polynomial RealInnerProductSpace ENNReal

namespace LovaszTheta.Circulant

/-- Coefficient of the normalized Hermite function. -/
noncomputable def hermiteCoefficient (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x, f x*normalizedHermite j x ∂gaussianReal 0 1

@[simp]
lemma hermiteCoefficient_zero (f : ℝ → ℝ) :
    hermiteCoefficient f 0 = ∫ x, f x ∂gaussianReal 0 1 := by
  simp [hermiteCoefficient, normalizedHermite]

lemma inner_hermiteL2_eq {f : ℝ → ℝ}
    (u : Lp ℝ 2 (gaussianReal 0 1)) (hu : u =ᵐ[gaussianReal 0 1] f) (j : ℕ) :
    ⟪u, hermiteL2 j⟫ = hermiteCoefficient f j := by
  rw [MeasureTheory.L2.inner_def, hermiteCoefficient]
  exact integral_congr_ae ((hu.and (hermiteL2_ae_eq j)).mono fun x h ↦ by
    simp only [h.1, h.2, RCLike.inner_apply, RCLike.conj_to_real, mul_comm])

/-- The closed span of the Hermite functions is the whole Gaussian L² space. -/
theorem span_hermiteL2_orthogonal_eq_bot :
    (Submodule.span ℝ (range hermiteL2))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  have hm := (Lp.memLp u).aestronglyMeasurable
  let f := hm.mk u
  have hEq : u =ᵐ[gaussianReal 0 1] f := hm.ae_eq_mk
  have hMeas : Measurable f := hm.stronglyMeasurable_mk.measurable
  have hf : MemLp f 2 (gaussianReal 0 1) := (memLp_congr_ae hEq).mp (Lp.memLp u)
  have h₀ (j : ℕ) : hermiteCoefficient f j = 0 := by
    rw [← inner_hermiteL2_eq u hEq]
    exact (Submodule.mem_orthogonal' _ _).mp hu _ (Submodule.subset_span (mem_range_self j))
  have hH (j : ℕ) : (∫ x, f x*(realHermite j).eval x ∂gaussianReal 0 1) = 0 := by
    have h := h₀ j
    simp only [hermiteCoefficient, normalizedHermite, ← mul_div_assoc, integral_div] at h
    have hS : Real.sqrt (j.factorial : ℝ) ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp h).resolve_right hS
  have hz := ae_eq_zero_of_gaussian_power_moments hMeas hf (integral_mul_pow_eq_zero_of_hermite f hf hH)
  simp only [Submodule.mem_bot]
  exact Lp.ext (hEq.trans (hz.trans (Lp.coeFn_zero _ _ _).symm))

/-- The normalized Hermite Hilbert basis of the standard Gaussian. -/
noncomputable def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermiteL2 span_hermiteL2_orthogonal_eq_bot

@[simp]
lemma hermiteBasis_apply (j : ℕ) : hermiteBasis j = hermiteL2 j := by
  unfold hermiteBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The Hermite series of a square-integrable function converges in L². -/
theorem hasSum_hermiteCoefficient {f : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    HasSum (fun j ↦ hermiteCoefficient f j • hermiteL2 j) (hf.toLp f) := by
  have hCoeff (j : ℕ) : hermiteBasis.repr (hf.toLp f) j = hermiteCoefficient f j := by
    rw [HilbertBasis.repr_apply_apply, hermiteBasis_apply, real_inner_comm]
    exact inner_hermiteL2_eq (hf.toLp f) hf.coeFn_toLp j
  simpa only [hCoeff, hermiteBasis_apply] using hermiteBasis.hasSum_repr (hf.toLp f)

/-- Parseval's identity for the Hermite coefficients. -/
theorem hasSum_sq_hermiteCoefficient {f : ℝ → ℝ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    HasSum (fun j ↦ hermiteCoefficient f j ^ 2) (∫ x, f x ^ 2 ∂gaussianReal 0 1) := by
  let u := hf.toLp f
  have h₁ (j : ℕ) : ⟪u, hermiteBasis j⟫ = hermiteCoefficient f j := by
    rw [hermiteBasis_apply]
    exact inner_hermiteL2_eq u hf.coeFn_toLp j
  have h₂ (j : ℕ) : ⟪hermiteBasis j, u⟫ = hermiteCoefficient f j := by
    rw [real_inner_comm]
    exact h₁ j
  have h₃ : ⟪u, u⟫ = ∫ x, f x^2 ∂gaussianReal 0 1 := by
    rw [MeasureTheory.L2.inner_def]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun x h ↦ by
      change u x = f x at h
      simp only [h, RCLike.inner_apply, RCLike.conj_to_real, pow_two])
  simpa only [h₁, h₂, ← pow_two, h₃] using hermiteBasis.hasSum_inner_mul_inner u u

end LovaszTheta.Circulant
