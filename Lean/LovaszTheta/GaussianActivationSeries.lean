module

public import LovaszTheta.HermiteSeriesLimit

/-!
# Centered activation on the Gaussian line

Pulling back the one-dimensional Hermite expansion by the unit
Gaussian series is an L² isometry. Removing its mean leaves a
convergent expansion in the positive even product span.
-/

@[expose] public section

open Finset Filter MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace NNReal ENNReal Topology

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- A measurable version of a Gaussian linear combination. -/
noncomputable def gaussianSeriesMeasurable (a : lp (fun _ : I ↦ ℝ) 2) : (I → ℝ) → ℝ :=
  (Lp.memLp (gaussianSeries I a)).aestronglyMeasurable.aemeasurable.mk (gaussianSeries I a)

lemma gaussianSeriesMeasurable_ae_eq (a : lp (fun _ : I ↦ ℝ) 2) :
    gaussianSeriesMeasurable a =ᵐ[gaussianProduct I] gaussianSeries I a :=
  ((Lp.memLp (gaussianSeries I a)).aestronglyMeasurable.aemeasurable.ae_eq_mk).symm

lemma gaussianSeriesMeasurable_measurePreserving (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    MeasurePreserving (gaussianSeriesMeasurable a) (gaussianProduct I) (gaussianReal 0 1) where
  measurable := (Lp.memLp (gaussianSeries I a)).aestronglyMeasurable.aemeasurable.measurable_mk
  map_eq := by rw [Measure.map_congr (gaussianSeriesMeasurable_ae_eq a),map_gaussianSeries,ha,one_pow,Real.toNNReal_one]

/-- Pull back the standard Gaussian L² space along the unit Gaussian series. -/
noncomputable def gaussianLinePullback (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    Lp ℝ 2 (gaussianReal 0 1) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct I) :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (gaussianSeriesMeasurable_measurePreserving a ha)

lemma gaussianLinePullback_ae_eq (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1)
    (v : Lp ℝ 2 (gaussianReal 0 1)) (f : ℝ → ℝ) (hf : v =ᵐ[gaussianReal 0 1] f) :
    gaussianLinePullback a ha v =ᵐ[gaussianProduct I] fun x ↦ f (gaussianSeries I a x) := by
  let M := gaussianSeriesMeasurable_measurePreserving a ha
  exact (Lp.coeFn_compMeasurePreserving v M).trans ((M.quasiMeasurePreserving.ae_eq_comp hf).trans
    ((gaussianSeriesMeasurable_ae_eq a).mono fun x hx ↦ congrArg f hx))

lemma gaussianLinePullback_hermiteL2 (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) (j : ℕ) :
    gaussianLinePullback a ha (hermiteL2 j) = gaussianHermiteL2 j a :=
  Lp.ext ((gaussianLinePullback_ae_eq a ha _ _ (hermiteL2_ae_eq j)).trans (gaussianHermiteL2_ae_eq j a).symm)

lemma memLp_scaledActivation {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) :
    MemLp (fun g ↦ activation τ (σ*g)) 2 (gaussianReal 0 1) :=
  (hasPolynomialGrowth_scaled_activation hτ σ).memLp_gaussian_two (continuous_scaled_activation τ σ) 1

/-- The activation of the Gaussian series, with its constant coefficient removed. -/
noncomputable def centeredGaussianActivation {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) : Lp ℝ 2 (gaussianProduct I) :=
  gaussianLinePullback a ha ((memLp_scaledActivation hτ σ).toLp (fun g ↦ activation τ (σ*g)) -
    activationMean τ σ • hermiteL2 0)

lemma centeredGaussianActivation_ae_eq {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    centeredGaussianActivation hτ σ a ha =ᵐ[gaussianProduct I]
      fun x ↦ activation τ (σ*gaussianSeries I a x) - activationMean τ σ := by
  refine gaussianLinePullback_ae_eq a ha _ (fun g ↦ activation τ (σ*g) - activationMean τ σ) ?_
  have h := (memLp_scaledActivation hτ σ).coeFn_toLp
  filter_upwards [h,hermiteL2_ae_eq 0,Lp.coeFn_smul (activationMean τ σ) (hermiteL2 0),
    Lp.coeFn_sub ((memLp_scaledActivation hτ σ).toLp _) (activationMean τ σ • hermiteL2 0)] with x hx h₀ h₁ h₂
  rw [h₂,Pi.sub_apply,hx,h₁,Pi.smul_apply,smul_eq_mul,h₀]
  simp [normalizedHermite]

/-- The removed mean is the expectation of the activation. -/
lemma integral_gaussianSeries_activation (τ σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    (∫ x, activation τ (σ*gaussianSeries I a x) ∂gaussianProduct I) = activationMean τ σ := by
  have hM := (Lp.memLp (gaussianSeries I a)).aestronglyMeasurable.aemeasurable
  rw [← integral_map hM (continuous_scaled_activation τ σ).aestronglyMeasurable,
    map_gaussianSeries,ha,one_pow,Real.toNNReal_one]
  rfl

/-- The nonconstant one-dimensional Hermite expansion pulled back to the Gaussian line. -/
theorem hasSum_centeredGaussianActivation {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    HasSum (fun j : ℕ ↦ activationCoefficient τ σ (j+1) • gaussianHermiteL2 (j+1) a)
      (centeredGaussianActivation hτ σ a ha) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_hermiteCoefficient (memLp_scaledActivation hτ σ))
  simp only [sum_range_one] at h
  change HasSum (fun j : ℕ ↦ activationCoefficient τ σ (j+1) • hermiteL2 (j+1))
    ((memLp_scaledActivation hτ σ).toLp (fun g ↦ activation τ (σ*g)) - activationCoefficient τ σ 0 • hermiteL2 0) at h
  rw [activationCoefficient_zero] at h
  have hP := h.mapL (gaussianLinePullback a ha).toContinuousLinearMap
  simpa only [LinearIsometry.coe_toContinuousLinearMap,map_smul,gaussianLinePullback_hermiteL2,
    centeredGaussianActivation] using hP

/-- The centered activation belongs to the closed span with positive even total degrees. -/
theorem centeredGaussianActivation_mem_even_span {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    centeredGaussianActivation hτ σ a ha ∈
      (Submodule.span ℝ (Set.range (fun m : PositiveEvenHermiteIndex I ↦ hermiteProductL2 m.val))).topologicalClosure := by
  let S := (Submodule.span ℝ
    (Set.range (fun m : PositiveEvenHermiteIndex I ↦ hermiteProductL2 m.val))).topologicalClosure
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hasSum_centeredGaussianActivation hτ σ a ha)
  exact Eventually.of_forall fun h ↦ Submodule.sum_mem S fun j _ ↦ by
    by_cases hj : Even (j+1)
    · apply Submodule.smul_mem S
      apply gaussianHermiteL2_mem_closedSpan (j+1) a ha
      intro m hm
      rw [hm]
      exact ⟨Nat.succ_pos _,hj⟩
    · rw [activationCoefficient_eq_zero_of_odd τ σ (Nat.not_even_iff_odd.mp hj),zero_smul]
      exact S.zero_mem

/-- The multivariate coefficient is the univariate Hermite
coefficient times the generating-function coefficient of the direction. -/
theorem inner_centeredGaussianActivation {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) (m : PositiveEvenHermiteIndex I) :
    ⟪centeredGaussianActivation hτ σ a ha,hermiteProductL2 m.val⟫ =
      activationCoefficient τ σ m.val.toMultiset.card * hermiteLinearCoeff a m.val := by
  let d := m.val.toMultiset.card
  let L := innerSL ℝ (hermiteProductL2 m.val)
  have h := (hasSum_centeredGaussianActivation hτ σ a ha).mapL L
  have hTerm (j : ℕ) : L (activationCoefficient τ σ (j+1) • gaussianHermiteL2 (j+1) a) =
      if j = d-1 then activationCoefficient τ σ d * hermiteLinearCoeff a m.val else 0 := by
    rw [map_smul,smul_eq_mul]
    unfold L
    rw [innerSL_apply_apply,real_inner_comm,inner_gaussianHermiteL2 (j+1) a ha]
    have hd : 0 < d := m.property.1
    by_cases hj : d = j+1
    · rw [ite_eq_left hj,ite_eq_left (show j = d-1 by omega),hj]
    · rw [ite_eq_right hj,ite_eq_right (show j ≠ d-1 by omega),mul_zero]
  simp only [hTerm] at h
  have hC := h.tsum_eq
  simp only [tsum_ite_eq, L, innerSL_apply_apply] at hC
  rw [real_inner_comm]
  exact hC.symm

end LovaszTheta.Circulant
