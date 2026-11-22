module

public import LovaszTheta.FiniteHermiteProducts
public import LovaszTheta.GaussianEquation

/-!
# Grafting on the Gaussian projection

The finite Hermite product coefficients are the coefficients used by
the Gaussian grafting isometry. The centered projection differs
from the centered activation by the Hermite tail in L².
-/

@[expose] public section

open Finset Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal RealInnerProductSpace

namespace LovaszTheta.Circulant

/-- Express the L² norm square as an ordinary integral. -/
lemma lp_two_norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (u : Lp ℝ 2 μ) : ‖u‖^2 = ∫ x, (u x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,pow_two]

namespace EvenTreeType

/-- One Hermite product viewed in the domain subspace of Gaussian grafting. -/
noncomputable def hermiteProductInEvenSpan (m : PositiveEvenHermiteIndex EvenTreeType) :
    evenHermiteSeries.toLinearMap.range :=
  ⟨hermiteProductL2 m.val,⟨lp.single 2 m 1,evenHermiteSeries_single m⟩⟩

/-- The centered finite projection, in the domain of the grafting isometry. -/
noncomputable def projectionInEvenSpan (τ v : ℝ) (s : Finset EvenTreeType) (M : ℕ) (u : EvenTreeType → ℝ) :
    evenHermiteSeries.toLinearMap.range :=
  ∑ m ∈ finiteHermiteProducts s M,
    activationHermiteProductCoeff τ v u m.val • hermiteProductInEvenSpan m

/-- The finite grafted Gaussian sum. -/
noncomputable def graftedActivationSeries (τ v : ℝ) (s : Finset EvenTreeType) (M : ℕ) (u : EvenTreeType → ℝ) :
    Lp ℝ 2 (gaussianProduct EvenTreeType) :=
  ∑ m ∈ finiteHermiteProducts s M,
    activationHermiteProductCoeff τ v u m.val • gaussianCoordinateL2 (graftOfIndex m)

lemma gaussianGraftIsometry_projectionInEvenSpan (τ v : ℝ) (s : Finset EvenTreeType) (M : ℕ)
    (u : EvenTreeType → ℝ) :
    gaussianGraftIsometry (projectionInEvenSpan τ v s M u) = graftedActivationSeries τ v s M u := by
  unfold projectionInEvenSpan graftedActivationSeries
  rw [map_sum]
  simp only [map_smul,hermiteProductInEvenSpan,gaussianGraftIsometry_hermiteProduct]

lemma projectionInEvenSpan_ae_eq {τ v : ℝ} (hv : v ≠ 0) (s : Finset EvenTreeType) (M : ℕ)
    (u : lp (fun _ : EvenTreeType ↦ ℝ) 2) (hu : ‖u‖ = 1) (hSupp : ∀ i ∉ s, u i = 0) :
    (projectionInEvenSpan τ v s M u).val =ᵐ[gaussianProduct EvenTreeType]
      fun x ↦ activationProjection τ v M (v*gaussianSeries EvenTreeType u x) - activationMean τ v := by
  let F := finiteHermiteProducts s M
  let c (m : PositiveEvenHermiteIndex EvenTreeType) := activationHermiteProductCoeff τ v u m.val
  have he : (projectionInEvenSpan τ v s M u).val = ∑ m ∈ F, c m • hermiteProductL2 m.val := by
    unfold projectionInEvenSpan
    simp only [Submodule.coe_sum,Submodule.coe_smul,hermiteProductInEvenSpan,F,c]
  have hSum : (∑ m ∈ F, c m • hermiteProductL2 m.val) =ᵐ[gaussianProduct EvenTreeType]
      fun x ↦ ∑ m ∈ F, c m * hermiteProduct m.val x := by
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    rw [show (fun x ↦ ∑ m ∈ F, c m * hermiteProduct m.val x) =
        ∑ m ∈ F, (fun x ↦ c m * hermiteProduct m.val x) by
          funext x
          exact (Finset.sum_apply x F (fun m y ↦ c m*hermiteProduct m.val y)).symm]
    exact eventuallyEq_sum fun m _ ↦ (Lp.coeFn_smul (c m) (hermiteProductL2 m.val)).trans
      ((hermiteProductL2_ae_eq m.val).mono fun x hx ↦ by rw [Pi.smul_apply,smul_eq_mul,hx])
  have hU : ∑ i ∈ s, u i^2 = 1 := by rw [sum_sq_eq_gaussianCoefficient_norm_sq hSupp,hu,one_pow]
  have hSeries := gaussianSeries_finsetSum_ae s u
  change gaussianSeries EvenTreeType (truncateCoefficients u s) =ᵐ[gaussianProduct EvenTreeType]
    fun x ↦ ∑ i ∈ s, u i*x i at hSeries
  rw [truncateCoefficients_eq_self hSupp] at hSeries
  rw [he]
  apply hSum.trans
  filter_upwards [hSeries] with x hx
  rw [hx,activationProjection_eq_hermiteProducts hv s M u x hU]
  dsimp only [F,c]
  ring

/-- The L² error of the centered projection is the Gaussian Hermite tail. -/
theorem norm_sq_activationInEvenSpan_sub_projection_le {τ v : ℝ} (hτ : 0 ≤ τ) (hv : 0 < v)
    (s : Finset EvenTreeType) (M : ℕ)
    (u : lp (fun _ : EvenTreeType ↦ ℝ) 2) (hu : ‖u‖ = 1) (hSupp : ∀ i ∉ s, u i = 0) :
    ‖activationInEvenSpan hτ v u hu - projectionInEvenSpan τ v s M u‖^2 =
      ∑' j : ℕ, activationCoefficient τ v (j+(M+1))^2 := by
  let a := activationInEvenSpan hτ v u hu
  let b := projectionInEvenSpan τ v s M u
  change ‖a.val-b.val‖^2 = _
  rw [lp_two_norm_sq_eq_integral]
  have he : (fun x ↦ ((a.val-b.val) x)^2) =ᵐ[gaussianProduct EvenTreeType]
      fun x ↦ (activationProjection τ v M (v*gaussianSeries EvenTreeType u x) -
        activation τ (v*gaussianSeries EvenTreeType u x))^2 := by
    filter_upwards [Lp.coeFn_sub a.val b.val,centeredGaussianActivation_ae_eq hτ v u hu,
      projectionInEvenSpan_ae_eq hv.ne' s M u hu hSupp] with x hx ha hb
    rw [hx,Pi.sub_apply,show a.val x = _ from ha,show b.val x = _ from hb]
    ring
  rw [integral_congr_ae he]
  let f (x : ℝ) := (activationProjection τ v M x-activation τ x)^2
  let g (x : EvenTreeType → ℝ) := v*gaussianSeries EvenTreeType u x
  have hM : AEMeasurable g (gaussianProduct EvenTreeType) :=
    aemeasurable_const.mul (Lp.memLp _).aestronglyMeasurable.aemeasurable
  have hC : Continuous f := ((contDiff_activationProjection τ v M).continuous.sub (continuous_activation τ)).pow _
  have hMap : (gaussianProduct EvenTreeType).map g = gaussianReal 0 ⟨v^2,sq_nonneg _⟩ := by
    rw [show g = (fun y : ℝ ↦ v*y) ∘ gaussianSeries EvenTreeType u from rfl]
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      ((Lp.memLp (gaussianSeries EvenTreeType u)).aestronglyMeasurable.aemeasurable),
      map_gaussianSeries,hu,one_pow,Real.toNNReal_one,gaussianReal_map_const_mul,mul_zero,mul_one]
    rfl
  change (∫ x, f (g x) ∂gaussianProduct EvenTreeType) = _
  rw [← integral_map hM hC.aestronglyMeasurable,hMap]
  exact integral_activationProjection_sub_sq hτ hv M

end EvenTreeType

end LovaszTheta.Circulant
