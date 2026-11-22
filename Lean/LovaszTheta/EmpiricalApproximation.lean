module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# Approximation by an empirical mean

For the Fourier net, approximate a convex combination of atoms by the mean of
independent samples from its coefficients. Hoeffding's inequality and the union
bound apply to all real and imaginary parts of the Fourier coordinates.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace LovaszTheta.Circulant

private lemma sampleMean_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) {R t : ℝ} (hR : 0 < R)
    (hBound : ∀ a, |f a| ≤ R) (ht : 0 ≤ t) {m : ℕ} (hm : 0 < m) :
    (Measure.pi (fun _ : Fin m ↦ μ)).real
        {w : Fin m → Ω | t ≤ |(∑ i, f (w i)) / (m : ℝ) - ∫ a, f a ∂μ|} ≤
      2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
  let ν := Measure.pi (fun _ : Fin m ↦ μ)
  let a := ∫ v, f v ∂μ
  let X (i : Fin m) (w : Fin m → Ω) := f (w i) - a
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hParam : (‖R - -R‖₊ / 2) ^ 2 = c := by
    apply NNReal.eq
    change (((‖R - -R‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = R ^ 2
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, NNReal.coe_ofNat, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    ring
  have hSingle : HasSubgaussianMGF (fun v ↦ f v - a) c μ := by
    rw [← hParam]
    apply hasSubgaussianMGF_of_mem_Icc hf.aemeasurable
    exact ae_of_all _ fun v ↦ abs_le.mp (hBound v)
  have hi : iIndepFun X ν :=
    iIndepFun_pi (X := fun _ : Fin m ↦ fun v ↦ f v - a) (fun _ ↦
      (hf.sub_const a).aemeasurable)
  have hSub (i : Fin m) : HasSubgaussianMGF (X i) c ν := by
    have hPres : MeasurePreserving (Function.eval i) ν μ :=
      measurePreserving_eval (μ := fun _ : Fin m ↦ μ) i
    have hMap : HasSubgaussianMGF (fun v ↦ f v - a) c (ν.map (Function.eval i)) := by
      rw [hPres.map_eq]
      exact hSingle
    exact .of_map hPres.measurable.aemeasurable hMap
  let S (w : Fin m → Ω) := ∑ i, X i w
  have hSG : HasSubgaussianMGF S (∑ _ : Fin m, c) ν :=
    HasSubgaussianMGF.sum_of_iIndepFun hi (fun i _ ↦ hSub i)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let u := (m : ℝ) * t
  have hu : 0 ≤ u := mul_nonneg hmR.le ht
  let badPos := {w : Fin m → Ω | u ≤ S w}
  let badNeg := {w : Fin m → Ω | u ≤ (-S) w}
  have hBad : {w : Fin m → Ω | t ≤ |(∑ i, f (w i)) / (m : ℝ) - a|} =
      badPos ∪ badNeg := by
    ext w
    have hSum : S w = (m : ℝ) * ((∑ i, f (w i)) / (m : ℝ) - a) := by
      simp only [S, X, Finset.sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_sub]
      field_simp
    change t ≤ |(∑ i, f (w i)) / (m : ℝ) - a| ↔ (u ≤ S w ∨ u ≤ -S w)
    rw [← le_max_iff, ← abs_eq_max_neg, hSum, abs_mul, abs_of_pos hmR]
    exact (mul_le_mul_iff_right₀ hmR).symm
  have hE :
      -(u ^ 2) / (2 * (↑(∑ _ : Fin m, c) : ℝ)) = -(m : ℝ) * t ^ 2 / (2 * R ^ 2) := by
    have hC : (↑(∑ _ : Fin m, c) : ℝ) = (m : ℝ) * R ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
      rfl
    rw [hC]
    dsimp [u]
    field_simp
  change ν.real {w : Fin m → Ω | t ≤ |(∑ i, f (w i)) / (m : ℝ) - a|} ≤ _
  rw [hBad]
  calc
    _ ≤ ν.real badPos + ν.real badNeg := measureReal_union_le _ _
    _ ≤ Real.exp (-(u ^ 2) / (2 * (↑(∑ _ : Fin m, c) : ℝ))) +
        Real.exp (-(u ^ 2) / (2 * (↑(∑ _ : Fin m, c) : ℝ))) :=
      add_le_add (hSG.measure_ge_le hu) (hSG.neg.measure_ge_le hu)
    _ = _ := by rw [hE, ← two_mul]

/-- A sample mean approximates all complex coordinates if the union of the
Hoeffding error probabilities is less than one. -/
theorem exists_empirical_mean {Ω ι : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (g : Ω → ι → ℂ) (z : ι → ℂ)
    (hmRe : ∀ i, Measurable fun a ↦ (g a i).re) (hmIm : ∀ i, Measurable fun a ↦ (g a i).im)
    (hzRe : ∀ i, ∫ a, (g a i).re ∂μ = (z i).re)
    (hzIm : ∀ i, ∫ a, (g a i).im ∂μ = (z i).im)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (hBound : ∀ a i, ‖g a i‖ ≤ R)
    {m : ℕ} (hm : 0 < m)
    (hTail : 4 * Fintype.card ι * Real.exp (-(m : ℝ) * u ^ 2 / (32 * R ^ 2)) < 1) :
    ∃ w : Fin m → Ω, ∀ i, ‖((∑ j, g (w j) i) / (m : ℂ)) - z i‖ ≤ u / 2 := by
  let ν := Measure.pi (fun _ : Fin m ↦ μ)
  let p (w : Fin m → Ω) (i : ι) := (∑ j, g (w j) i) / (m : ℂ) - z i
  let bad (i : ι) := {w | u / 4 ≤ |(p w i).re|} ∪ {w | u / 4 ≤ |(p w i).im|}
  let e := Real.exp (-(m : ℝ) * u ^ 2 / (32 * R ^ 2))
  have hRe (i : ι) : ν.real {w | u / 4 ≤ |(p w i).re|} ≤ 2 * e := by
    have h := sampleMean_abs_tail (μ := μ) (fun a ↦ (g a i).re) (hmRe i) hR
      (fun a ↦ (Complex.abs_re_le_norm _).trans (hBound a i)) (by positivity : 0 ≤ u / 4) hm
    have hP (w : Fin m → Ω) : (p w i).re = (∑ j, (g (w j) i).re) / (m : ℝ) - (z i).re := by
      simp only [p, Complex.sub_re, Complex.div_natCast_re, Complex.re_sum]
    simp_rw [hzRe, ← hP] at h
    convert h using 3
    ring
  have hIm (i : ι) : ν.real {w | u / 4 ≤ |(p w i).im|} ≤ 2 * e := by
    have h := sampleMean_abs_tail (μ := μ) (fun a ↦ (g a i).im) (hmIm i) hR
      (fun a ↦ (Complex.abs_im_le_norm _).trans (hBound a i)) (by positivity : 0 ≤ u / 4) hm
    have hP (w : Fin m → Ω) : (p w i).im = (∑ j, (g (w j) i).im) / (m : ℝ) - (z i).im := by
      simp only [p, Complex.sub_im, Complex.div_natCast_im, Complex.im_sum]
    simp_rw [hzIm, ← hP] at h
    convert h using 3
    ring
  have hB : ν.real (⋃ i, bad i) < 1 := by
    calc
      _ ≤ ∑ i, ν.real (bad i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : ι, 4 * e := sum_le_sum fun i _ ↦ by
        exact (measureReal_union_le _ _).trans (by linarith [hRe i, hIm i])
      _ < _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul, e]
        linarith only [hTail]
  have hEx : ∃ w : Fin m → Ω, w ∉ ⋃ i, bad i := by
    by_contra! h
    have hAll : (⋃ i, bad i) = Set.univ := Set.eq_univ_of_forall h
    rw [hAll] at hB
    have hOne : ν.real Set.univ = 1 := by simp
    exact (not_lt_of_ge hOne.ge) hB
  obtain ⟨w, hw⟩ := hEx
  refine ⟨w, fun i ↦ ?_⟩
  have hi : w ∉ bad i := fun hi ↦ hw (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hiRe : |(p w i).re| < u / 4 := lt_of_not_ge fun h ↦ hi (Or.inl h)
  have hiIm : |(p w i).im| < u / 4 := lt_of_not_ge fun h ↦ hi (Or.inr h)
  exact (Complex.norm_le_abs_re_add_abs_im (p w i)).trans (by linarith)

end LovaszTheta.Circulant
