module

public import LovaszTheta.HermiteGrafting
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Law of the Gaussian series

Finite coordinate sums are centered Gaussians. Their
characteristic functions converge under L² convergence by a
Lipschitz bound, and the variances converge by square summability.
-/

@[expose] public section

open Finset Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal Topology

namespace LovaszTheta.Circulant

private lemma norm_exp_imag_sub_le (x y t : ℝ) :
    ‖Complex.exp ((t : ℂ)*x*Complex.I) - Complex.exp ((t : ℂ)*y*Complex.I)‖ ≤ |t| * |x-y| := by
  have he : ((t : ℂ)*x*Complex.I) = (t : ℂ)*y*Complex.I + Complex.I * (↑(t*(x-y)) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← mul_sub_one, norm_mul]
  have h1 : ‖Complex.exp ((t : ℂ)*y*Complex.I)‖ = 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [h1,one_mul]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(x-y))).trans_eq
    (by rw [Real.norm_eq_abs,abs_mul])

private lemma integral_norm_l2_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) : ∫ x, ‖f x‖ ∂μ ≤ ‖f‖ := by
  have hInt := (memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent one_le_two))
  have he : (∫ x, ‖hInt.toL1 f x‖ ∂μ) = ∫ x, ‖f x‖ ∂μ :=
    integral_congr_ae (hInt.coeFn_toL1.mono fun x h ↦ congrArg Norm.norm h)
  rw [← he, ← L1.norm_eq_integral_norm, Integrable.toL1, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

/-- Characteristic functions are continuous under L² convergence on a probability space. -/
lemma continuous_l2_charFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (t : ℝ) : Continuous (fun f : Lp ℝ 2 μ ↦ charFun (μ.map f) t) := by
  refine (LipschitzWith.of_dist_le_mul (K := |t|.toNNReal) (fun f g ↦ ?_)).continuous
  let ψ (z : ℝ) := Complex.exp ((t : ℂ)*z*Complex.I)
  have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
  have hz (z : ℝ) : ‖ψ z‖ = 1 := by
    dsimp [ψ]
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hm (v : Lp ℝ 2 μ) : AEMeasurable v μ := (Lp.memLp v).aestronglyMeasurable.aemeasurable
  have hi (v : Lp ℝ 2 μ) : Integrable (fun x ↦ ψ (v x)) μ :=
    (integrable_const (1 : ℝ)).mono' (hψ.comp_aemeasurable (hm v)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ (hz (v x)).le)
  have he (v : Lp ℝ 2 μ) : charFun (μ.map v) t = ∫ x, ψ (v x) ∂μ := by
    rw [charFun_apply_real]
    exact integral_map (hm v) hψ.aestronglyMeasurable
  simp only [dist_eq_norm, he, ← integral_sub (hi f) (hi g), Real.coe_toNNReal _ (abs_nonneg _)]
  have hle : ∀ᵐ x ∂μ, ‖ψ (f x)-ψ (g x)‖ ≤ |t| * ‖(f-g) x‖ :=
    (Lp.coeFn_sub f g).mono fun x hx ↦ by
      simpa only [hx,Pi.sub_apply,Real.norm_eq_abs] using norm_exp_imag_sub_le (f x) (g x) t
  calc
    _ ≤ ∫ x, ‖ψ (f x)-ψ (g x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| * ‖(f-g) x‖ ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (((Lp.memLp (f-g)).integrable one_le_two).norm.const_mul _) hle
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_l2_le (f-g)) (abs_nonneg _)

variable {I : Type*}

/-- The Gaussian law of a finite coordinate sum on the product space. -/
lemma map_gaussianProduct_sum (s : Finset I) (a : I → ℝ) :
    (gaussianProduct I).map (fun x ↦ ∑ i ∈ s, a i*x i) =
      gaussianReal 0 (∑ i ∈ s, a i^2).toNNReal := by
  let f (x : s → ℝ) := ∑ i : s, a i.val*x i
  have hF (x : I → ℝ) : f (s.restrict x) = ∑ i ∈ s, a i*x i := sum_coe_sort s fun i ↦ a i*x i
  simp only [← hF]
  change (gaussianProduct I).map (f ∘ s.restrict) = _
  rw [← Measure.map_map (measurable_coordinate_sum (fun i : s ↦ a i.val)) (measurable_restrict s),
    (gaussianProduct_restrict s).map_eq]
  exact (map_gaussianCoordinates_sum (fun i : s ↦ a i.val)).trans
    (congrArg (fun v : ℝ ↦ gaussianReal 0 v.toNNReal) (sum_coe_sort s fun i ↦ a i^2))

lemma gaussianSeries_finsetSum_ae (s : Finset I) (a : I → ℝ) :
    gaussianSeries I (∑ i ∈ s, lp.single 2 i (a i)) =ᵐ[gaussianProduct I]
      fun x ↦ ∑ i ∈ s, a i*x i := by
  rw [map_sum]
  simp only [gaussianSeries,orthonormalSeries_single]
  refine (Lp.coeFn_finsetSum s _).trans ?_
  rw [show (fun x : I → ℝ ↦ ∑ i ∈ s, a i*x i) = ∑ i ∈ s, (fun x ↦ a i*x i) by
    funext x; rw [Finset.sum_apply]]
  apply eventuallyEq_sum
  intro i _
  exact (Lp.coeFn_smul (a i) (gaussianCoordinateL2 i)).trans
    ((gaussianCoordinateL2_ae_eq i).mono fun x hx ↦ by simp only [Pi.smul_apply,smul_eq_mul,hx])

/-- Every square-summable Gaussian linear combination has the
centered Gaussian law with the prescribed variance. -/
theorem map_gaussianSeries (a : lp (fun _ : I ↦ ℝ) 2) :
    (gaussianProduct I).map (gaussianSeries I a) = gaussianReal 0 (‖a‖^2).toNNReal := by
  let v (s : Finset I) := ∑ i ∈ s, (a i)^2
  have hA : Tendsto (fun s : Finset I ↦ ∑ i ∈ s, lp.single 2 i (a i)) atTop (𝓝 a) :=
    lp.hasSum_single (by norm_num) a
  have hV : Tendsto v atTop (𝓝 (‖a‖^2)) := by
    have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at h
    exact h
  apply Measure.ext_of_charFun
  funext t
  have hCont := (continuous_l2_charFun (μ := gaussianProduct I) t).continuousAt (x := gaussianSeries I a)
  have hLeft := hCont.tendsto.comp ((gaussianSeries I).continuous.continuousAt.tendsto.comp hA)
  have hRight : Tendsto (fun s : Finset I ↦ charFun (gaussianReal 0 (v s).toNNReal) t) atTop
      (𝓝 (charFun (gaussianReal 0 (‖a‖^2).toNNReal) t)) := by
    have hF : Continuous (fun x : ℝ ↦ charFun (gaussianReal 0 x.toNNReal) t) := by
      simp only [charFun_gaussianReal]
      fun_prop
    exact hF.continuousAt.tendsto.comp hV
  apply tendsto_nhds_unique _ hRight
  convert hLeft using 1
  funext s
  rw [Function.comp_apply, Function.comp_apply, Measure.map_congr (gaussianSeries_finsetSum_ae s a),
    map_gaussianProduct_sum]

end LovaszTheta.Circulant
