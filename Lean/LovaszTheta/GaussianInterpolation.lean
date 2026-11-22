module

public import LovaszTheta.GaussianIntegration
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Interpolation with a Gaussian

For a fixed value of a sign polynomial, differentiate its mixture
with an independent Gaussian inside the integral. Gaussian
integration by parts removes the derivative of the Gaussian weight.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace LovaszTheta.Circulant

/-- The interpolation from a centered Gaussian sample to a sign coordinate. -/
noncomputable def gaussianBlend (t y g : ℝ) : ℝ :=
  Real.sqrt t * y + Real.sqrt (1-t) * g

lemma one_add_abs_gaussianBlend_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (y g : ℝ) :
    1 + |gaussianBlend t y g| ≤ (1+|y|) * (1+|g|) := by
  have ha : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht.2
  have hb : Real.sqrt (1-t) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (show 1-t ≤ 1 by linarith [ht.1])
  have hy : Real.sqrt t * |y| ≤ |y| := by exact mul_le_of_le_one_left (abs_nonneg y) ha
  have hg : Real.sqrt (1-t) * |g| ≤ |g| := by exact mul_le_of_le_one_left (abs_nonneg g) hb
  have hTri := abs_add_le (Real.sqrt t*y) (Real.sqrt (1-t)*g)
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hTri
  unfold gaussianBlend
  nlinarith only [hTri, hy, hg, mul_nonneg (abs_nonneg y) (abs_nonneg g)]

private lemma abs_test_gaussianBlend_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (y g C : ℝ) (r : ℕ) (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hf : ∀ x, |f x| ≤ C * (1+|x|)^r) :
    |f (gaussianBlend t y g)| ≤ (C * (1+|y|)^r) * (1+|g|)^r := by
  calc
    _ ≤ C * (1+|gaussianBlend t y g|)^r := hf _
    _ ≤ C * ((1+|y|)*(1+|g|))^r :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (one_add_abs_gaussianBlend_le ht y g) _) hC
    _ = _ := by rw [mul_pow, mul_assoc]

private lemma hasDerivAt_gaussianBlend {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (y g : ℝ) :
    HasDerivAt (fun s ↦ gaussianBlend s y g)
      (y/(2*Real.sqrt t) - g/(2*Real.sqrt (1-t))) t := by
  have hleft := (Real.hasDerivAt_sqrt ht.1.ne').mul_const y
  have hsub := (hasDerivAt_id' t).const_sub (1 : ℝ)
  have hright := (hsub.sqrt (sub_ne_zero.mpr ht.2.ne')).mul_const g
  convert hleft.add hright using 1
  · rfl
  · ring

private lemma abs_gaussianBlend_derivative_le {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ ≤ t) (ht' : δ ≤ 1-t) (y g : ℝ) :
    |y/(2*Real.sqrt t) - g/(2*Real.sqrt (1-t))| ≤
      ((1+|y|)/(2*Real.sqrt δ)) * (1+|g|) := by
  have h0 : 0 < 2*Real.sqrt δ := by positivity
  have ha : 2*Real.sqrt δ ≤ 2*Real.sqrt t := by gcongr
  have hb : 2*Real.sqrt δ ≤ 2*Real.sqrt (1-t) := by gcongr
  calc
    _ ≤ |y/(2*Real.sqrt t)| + |g/(2*Real.sqrt (1-t))| := abs_sub _ _
    _ = |y|/(2*Real.sqrt t) + |g|/(2*Real.sqrt (1-t)) := by
      simp only [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 * Real.sqrt t by positivity),
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * Real.sqrt (1-t) by positivity)]
    _ ≤ |y|/(2*Real.sqrt δ) + |g|/(2*Real.sqrt δ) :=
      add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) h0 ha)
        (div_le_div_of_nonneg_left (abs_nonneg _) h0 hb)
    _ ≤ _ := by
      have hNum : |y| + |g| ≤ (1+|y|)*(1+|g|) := by
        nlinarith only [mul_nonneg (abs_nonneg y) (abs_nonneg g)]
      rw [← add_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hNum h0.le

/-- The interpolation integral is continuous on the closed interval,
including both endpoints. -/
theorem continuousOn_integral_gaussianBlend (v : ℝ≥0) (y C : ℝ) (r : ℕ)
    (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ x, |f x| ≤ C * (1+|x|)^r) :
    ContinuousOn (fun t ↦ ∫ g, f (gaussianBlend t y g) ∂gaussianReal 0 v) (Icc 0 1) := by
  intro t _
  let bound (g : ℝ) := (C*(1+|y|)^r)*(1+|g|)^r
  have hBound := integrable_growth_gaussian v r (C*(1+|y|)^r)
    (by unfold bound; fun_prop : Continuous bound) (fun g ↦ by
      dsimp [bound]
      exact abs_of_nonneg (by positivity) |>.le)
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hBound ?_
  · exact Eventually.of_forall fun s ↦ (hf.comp (by unfold gaussianBlend; fun_prop)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ae_of_all _ fun g ↦ by
      simpa only [Real.norm_eq_abs] using abs_test_gaussianBlend_le hs y g C r hC h
  · exact ae_of_all _ fun g ↦
      (hf.comp (by unfold gaussianBlend; fun_prop)).continuousAt.continuousWithinAt

private lemma hasDerivAt_integral_gaussianBlend_raw (v : ℝ≥0) (y C : ℝ) (r : ℕ)
    (hC : 0 ≤ C) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f f' : ℝ → ℝ}
    (hder : ∀ x, HasDerivAt f (f' x) x) (hCont' : Continuous f')
    (hf : ∀ x, |f x| ≤ C * (1+|x|)^r) (hf' : ∀ x, |f' x| ≤ C * (1+|x|)^r) :
    HasDerivAt (fun s ↦ ∫ g, f (gaussianBlend s y g) ∂gaussianReal 0 v)
      (∫ g, f' (gaussianBlend t y g) *
        (y/(2*Real.sqrt t) - g/(2*Real.sqrt (1-t))) ∂gaussianReal 0 v) t := by
  let δ := min (t/2) ((1-t)/2)
  have hδ : 0 < δ := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have htδ : t ∈ Ioo δ (1-δ) := by
    have h₁ : δ ≤ t/2 := min_le_left _ _
    have h₂ : δ ≤ (1-t)/2 := min_le_right _ _
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let A := C*(1+|y|)^r
  let B := (1+|y|)/(2*Real.sqrt δ)
  have hA : 0 ≤ A := by unfold A; positivity
  have hB : 0 ≤ B := by unfold B; positivity
  have hCont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hder x).continuousAt
  let F (s g : ℝ) := f (gaussianBlend s y g)
  let F' (s g : ℝ) := f' (gaussianBlend s y g) *
    (y/(2*Real.sqrt s) - g/(2*Real.sqrt (1-s)))
  have hFCont (s : ℝ) : Continuous (F s) := hCont.comp (by unfold gaussianBlend; fun_prop)
  have hF'Cont : Continuous (F' t) := by unfold F' gaussianBlend; fun_prop
  have hInt : Integrable (F t) (gaussianReal 0 v) :=
    integrable_growth_gaussian v r A (hFCont _) (fun g ↦ abs_test_gaussianBlend_le
      (Ioo_subset_Icc_self ht) y g C r hC hf)
  have hdom (s : ℝ) (hs : s ∈ Ioo δ (1-δ)) (g : ℝ) :
      ‖F' s g‖ ≤ (A*B)*(1+|g|)^(r+1) := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [Real.norm_eq_abs]
    change |f' (gaussianBlend s y g) *
      (y/(2*Real.sqrt s) - g/(2*Real.sqrt (1-s)))| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (A*(1+|g|)^r) * (B*(1+|g|)) :=
        mul_le_mul (abs_test_gaussianBlend_le hs' y g C r hC hf')
          (abs_gaussianBlend_derivative_le hδ hs.1.le (by linarith [hs.2]) y g)
          (abs_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hboundInt := integrable_growth_gaussian v (r+1) (A*B)
    (by fun_prop : Continuous fun g : ℝ ↦ (A*B)*(1+|g|)^(r+1))
    (fun _ ↦ (abs_of_nonneg (by positivity)).le)
  have hPoint (g s : ℝ) (hs : s ∈ Ioo δ (1-δ)) : HasDerivAt (F · g) (F' s g) s := by
    have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (hder _).comp s (hasDerivAt_gaussianBlend hs' y g)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 v)
    (Ioo_mem_nhds htδ.1 htδ.2)
    (Eventually.of_forall fun s ↦ (hFCont s).aestronglyMeasurable) hInt hF'Cont.aestronglyMeasurable
    (ae_of_all _ fun g s hs ↦ hdom s hs g) hboundInt (ae_of_all _ hPoint)).2

/-- On the open interval, the derivative of the interpolation equals
the sign term minus half the Gaussian variance times the second derivative. -/
theorem hasDerivAt_integral_gaussianBlend (v : ℝ≥0) (y C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    (hCont : Continuous f'')
    (hf : ∀ x, |f x| ≤ C * (1+|x|)^r)
    (hf' : ∀ x, |f' x| ≤ C * (1+|x|)^r)
    (hf'' : ∀ x, |f'' x| ≤ C * (1+|x|)^r) :
    HasDerivAt (fun s ↦ ∫ g, f (gaussianBlend s y g) ∂gaussianReal 0 v)
      ((y/(2*Real.sqrt t)) * (∫ g, f' (gaussianBlend t y g) ∂gaussianReal 0 v) -
        ((v : ℝ)/2) * (∫ g, f'' (gaussianBlend t y g) ∂gaussianReal 0 v)) t := by
  have ht' := Ioo_subset_Icc_self ht
  have hCont' : Continuous f' := continuous_iff_continuousAt.mpr fun x ↦ (hd' x).continuousAt
  have hraw := hasDerivAt_integral_gaussianBlend_raw v y C r hC ht hd hCont' hf hf'
  let A := C*(1+|y|)^r
  let G (g : ℝ) := f' (gaussianBlend t y g)
  let H (g : ℝ) := f'' (gaussianBlend t y g)
  let β := Real.sqrt (1-t)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβpos : 0 < β := Real.sqrt_pos.mpr (by linarith [ht.2])
  have hβ1 : β ≤ 1 := by
    unfold β
    simpa using Real.sqrt_le_sqrt (show 1-t ≤ 1 by linarith [ht.1])
  have hG : Continuous G := hCont'.comp (by unfold gaussianBlend; fun_prop)
  have hH : Continuous H := hCont.comp (by unfold gaussianBlend; fun_prop)
  have hGgrow (g : ℝ) : |G g| ≤ A*(1+|g|)^r := abs_test_gaussianBlend_le ht' y g C r hC hf'
  have hIbp := gaussian_integration_by_parts v r A (f := G) (f' := fun g ↦ β*H g)
    (fun g ↦ by
      have hb := ((hasDerivAt_id' g).const_mul β).const_add (Real.sqrt t * y)
      have hcomp := (hd' (gaussianBlend t y g)).comp g hb
      convert hcomp using 1 <;> first | rfl | simp [H, mul_comm]) (by fun_prop) hGgrow
    (fun g ↦ by
      rw [abs_mul, abs_of_nonneg hβ0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hβ1).trans
        (abs_test_gaussianBlend_le ht' y g C r hC hf''))
  have hIntegral := integrable_growth_gaussian v r A hG hGgrow
  have hMoment : Integrable (fun g ↦ g * G g) (gaussianReal 0 v) := by
    apply integrable_growth_gaussian v (r+1) A (by fun_prop)
    intro g
    rw [abs_mul, pow_succ, ← mul_assoc]
    calc
      _ ≤ |g| * (A*(1+|g|)^r) := mul_le_mul_of_nonneg_left (hGgrow _) (abs_nonneg _)
      _ = (A*(1+|g|)^r) * |g| := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ((abs_nonneg _).trans (hGgrow _))
  have hr : (∫ g, G g * (y/(2*Real.sqrt t) - g/(2*β)) ∂gaussianReal 0 v) =
      (y/(2*Real.sqrt t)) * (∫ g, G g ∂gaussianReal 0 v) -
        ((v : ℝ)/2) * (∫ g, H g ∂gaussianReal 0 v) := by
    have h (g : ℝ) : G g * (y/(2*Real.sqrt t) - g/(2*β)) =
        (y/(2*Real.sqrt t))*G g - (2*β)⁻¹*(g * G g) := by
      simp only [div_eq_mul_inv]
      ring
    simp_rw [h]
    rw [integral_sub (hIntegral.const_mul _) (hMoment.const_mul _),
      integral_const_mul, integral_const_mul, hIbp, integral_const_mul]
    congr 1
    field_simp [hβpos.ne']
  rw [← hr]
  exact hraw

end LovaszTheta.Circulant
