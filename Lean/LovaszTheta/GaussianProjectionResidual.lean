module

public import LovaszTheta.GaussianProjectionGraft
public import LovaszTheta.GaussianSizeProjection

/-!
# Residual of the truncated Gaussian equation

Centering contracts L², and the activation is Lipschitz. Together
with the grafting isometry, these facts bound the truncated
equation by the two squared tails.
-/

@[expose] public section

open MeasureTheory
open scoped Classical ENNReal

namespace LovaszTheta.Circulant

private lemma norm_sq_sub_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (u w : Lp ℝ 2 μ) (hw : w =ᵐ[μ] fun x ↦ u x - ∫ y, u y ∂μ) :
    ‖w‖^2 ≤ ‖u‖^2 := by
  let a := ∫ y, u y ∂μ
  have hA : Integrable (fun x ↦ 2*a*u x) μ := ((Lp.memLp u).integrable one_le_two).const_mul _
  have hU : Integrable (fun x ↦ (u x)^2) μ := by
    rw [show (fun x ↦ (u x)^2) = (u : Ω → ℝ)*(u : Ω → ℝ) from funext fun _ ↦ pow_two _]
    exact (Lp.memLp u).integrable_mul (Lp.memLp u)
  have hSub : Integrable (fun x ↦ (u x)^2-2*a*u x) μ := hU.sub hA
  have h := integral_congr_ae (hw.mono fun x hx ↦
    show (w x)^2 = (u x)^2-2*a*u x+a^2 by rw [hx]; change (u x-a)^2 = _; ring)
  rw [lp_two_norm_sq_eq_integral,lp_two_norm_sq_eq_integral,h,integral_add hSub (integrable_const _),
    integral_sub hU hA,integral_const_mul,integral_const,probReal_univ,one_smul]
  change (∫ x, (u x)^2 ∂μ) - 2*a*a+a^2 ≤ _
  nlinarith only [sq_nonneg a]

private lemma memLp_gaussianSeries_activation {I : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ)
    (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    MemLp (fun x ↦ activation τ (s*gaussianSeries I a x)) 2 (gaussianProduct I) := by
  have he := gaussianLinePullback_ae_eq a ha _ _ (memLp_scaledActivation hτ s).coeFn_toLp
  exact (memLp_congr_ae he).mp (Lp.memLp _)

theorem norm_sq_centeredGaussianActivation_sub_le {I : Type*} {τ : ℝ} (hτ : 0 < τ) (s v : ℝ)
    (a b : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖centeredGaussianActivation hτ.le s a ha - centeredGaussianActivation hτ.le v b hb‖^2 ≤
      ‖s • gaussianSeries I a - v • gaussianSeries I b‖^2 := by
  let μ := gaussianProduct I
  let f (x : I → ℝ) := activation τ (s*gaussianSeries I a x)
  let g (x : I → ℝ) := activation τ (v*gaussianSeries I b x)
  have hf : MemLp f 2 μ := memLp_gaussianSeries_activation hτ.le s a ha
  have hg : MemLp g 2 μ := memLp_gaussianSeries_activation hτ.le v b hb
  let w := (hf.sub hg).toLp (f-g)
  let u := centeredGaussianActivation hτ.le s a ha - centeredGaussianActivation hτ.le v b hb
  have hM : (∫ x, w x ∂μ) = activationMean τ s - activationMean τ v := by
    have he := integral_congr_ae (hf.sub hg).coeFn_toLp
    rw [show (∫ x, w x ∂μ) = ∫ x, (f-g) x ∂μ from he,
      show (∫ x, (f-g) x ∂μ) = (∫ x, f x ∂μ)-(∫ x, g x ∂μ) from
        integral_sub (hf.integrable one_le_two) (hg.integrable one_le_two)]
    exact congrArg₂ (· - ·) (integral_gaussianSeries_activation τ s a ha)
      (integral_gaussianSeries_activation τ v b hb)
  have hU : u =ᵐ[μ] fun x ↦ w x - ∫ y, w y ∂μ := by
    filter_upwards [centeredGaussianActivation_ae_eq hτ.le s a ha,
      centeredGaussianActivation_ae_eq hτ.le v b hb,(hf.sub hg).coeFn_toLp,
      Lp.coeFn_sub (centeredGaussianActivation hτ.le s a ha) (centeredGaussianActivation hτ.le v b hb)] with x h₁ h₂ h₃ h₄
    rw [h₄,Pi.sub_apply,h₁,h₂,show w x = (f-g) x from h₃,hM,Pi.sub_apply]
    unfold f g
    ring
  apply (norm_sq_sub_integral_le w u hU).trans
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(hf.sub hg).coeFn_toLp,Lp.coeFn_smul s (gaussianSeries I a),
    Lp.coeFn_smul v (gaussianSeries I b),
    Lp.coeFn_sub (s • gaussianSeries I a) (v • gaussianSeries I b)] with x h₀ h₁ h₂ h₃
  rw [show w x = (f-g) x from h₀,h₃,Pi.sub_apply,Pi.sub_apply,h₁,h₂]
  simpa only [Real.norm_eq_abs,Pi.smul_apply,smul_eq_mul,f,g] using
    abs_activation_sub_le hτ (s*gaussianSeries I a x) (v*gaussianSeries I b x)

namespace EvenTreeType

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))

/-- The centered finite projection and grafted sum leave an L² residual
controlled by the discarded sizes and degrees. -/
theorem norm_sq_gaussianProjection_residual_le {D : ℕ} (hD : 0 < D) (M : ℕ) :
    let H := σ • gaussianSeries EvenTreeType (gaussianCoefficientVector hτ hσ hσ' hMean)
    let H_D := gaussianSizeProjection hτ hσ hσ' hMean D
    let v := gaussianSizeScale hτ hσ hσ' hMean D
    let u := gaussianSizeDirection hτ hσ hσ' hMean D
    let Y := graftedActivationSeries τ v (typesThroughSize D) M u
    ‖H_D - (2 : ℝ) • gaussianCoordinateL2 leaf - Y‖^2 ≤
      6*‖H-H_D‖^2+3*(∑' j : ℕ, activationCoefficient τ v (j+(M+1))^2) := by
  let a := gaussianCoefficientVector hτ hσ hσ' hMean
  let H := σ • gaussianSeries EvenTreeType a
  let H_D := gaussianSizeProjection hτ hσ hσ' hMean D
  let v := gaussianSizeScale hτ hσ hσ' hMean D
  let u := gaussianSizeDirection hτ hσ hσ' hMean D
  let S := typesThroughSize D
  have ha : ‖a‖ = 1 := norm_gaussianCoefficientVector hτ hσ hσ' hMean
  have hu : ‖u‖ = 1 := norm_gaussianSizeDirection hτ hσ hσ' hMean hD
  have hv : 0 < v := zero_lt_two.trans_le (gaussianSizeScale_bounds hτ hσ hσ' hMean hD).1
  let A := activationInEvenSpan hτ.le σ a ha
  let B := activationInEvenSpan hτ.le v u hu
  let P := projectionInEvenSpan τ v S M u
  have hAB : ‖A-B‖^2 ≤ ‖H-H_D‖^2 := by
    have h := norm_sq_centeredGaussianActivation_sub_le hτ σ v a u ha hu
    rw [gaussianSizeScale_smul_series hτ hσ hσ' hMean hD] at h
    exact h
  have hBP : ‖B-P‖^2 = ∑' j : ℕ, activationCoefficient τ v (j+(M+1))^2 :=
    norm_sq_activationInEvenSpan_sub_projection_le hτ.le hv S M u hu
      (gaussianSizeDirection_apply_of_notMem hτ hσ hσ' hMean D)
  have hEq : H = (2 : ℝ) • gaussianCoordinateL2 leaf + gaussianGraftIsometry A :=
    gaussian_equation hτ hσ hσ' hMean
  change ‖H_D - (2 : ℝ) • gaussianCoordinateL2 leaf - graftedActivationSeries τ v S M u‖^2 ≤ _
  rw [← gaussianGraftIsometry_projectionInEvenSpan]
  have he : H_D - (2 : ℝ) • gaussianCoordinateL2 leaf - gaussianGraftIsometry P =
      (H_D-H) + gaussianGraftIsometry (A-B) + gaussianGraftIsometry (B-P) := by
    rw [map_sub,map_sub,hEq]
    abel
  rw [he]
  have hn : ‖(H_D-H)+gaussianGraftIsometry (A-B)+gaussianGraftIsometry (B-P)‖ ≤
      ‖H-H_D‖+‖A-B‖+‖B-P‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [gaussianGraftIsometry.norm_map]
    apply add_le_add_left
    exact (norm_add_le _ _).trans_eq (by rw [gaussianGraftIsometry.norm_map,norm_sub_rev])
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ?_
  nlinarith only [hAB,hBP,sq_nonneg (‖H-H_D‖-‖A-B‖),sq_nonneg (‖H-H_D‖-‖B-P‖),
    sq_nonneg (‖A-B‖-‖B-P‖)]

end EvenTreeType

end LovaszTheta.Circulant
