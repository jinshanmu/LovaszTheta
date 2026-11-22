module

public import LovaszTheta.EmpiricalApproximation
public import LovaszTheta.KernelIncrements

/-!
# Fourier nets from signed coordinate atoms

The ℓ¹ ball of radius R is the convex hull of zero and the signed coordinate
vectors of magnitude R. An empirical mean of these atoms gives the finite set
of possible centers. For a subset of the ball, choose a representative inside
the subset from each half-radius ball that meets it.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Classical ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The unnormalized Fourier transform on real vectors. -/
noncomputable def fourierReal : (ZMod n → ℝ) →ₗ[ℝ] (ZMod n → ℂ) :=
  ((ZMod.dft : (ZMod n → ℂ) ≃ₗ[ℂ] (ZMod n → ℂ)).toLinearMap.restrictScalars ℝ).comp
    (LinearMap.pi fun i : ZMod n ↦ Complex.ofRealAm.toLinearMap.comp (LinearMap.proj i))

lemma fourierReal_apply (x : ZMod n → ℝ) (k : ZMod n) :
    fourierReal x k = 𝓕 (fun j ↦ (x j : ℂ)) k := rfl

/-- The ℓ¹ norm in the counting convention. -/
noncomputable def ellOne (x : ZMod n → ℝ) : ℝ := ∑ i, |x i|

/-- The Fourier supremum distance used for chaining. -/
noncomputable def fourierDistance (x y : ZMod n → ℝ) : ℝ :=
  dist (fourierReal x) (fourierReal y)

lemma fourierDistance_comm (x y : ZMod n → ℝ) :
    fourierDistance x y = fourierDistance y x := dist_comm _ _

lemma fourierDistance_triangle (x y z : ZMod n → ℝ) :
    fourierDistance x z ≤ fourierDistance x y + fourierDistance y z := dist_triangle _ _ _

lemma fourierDistance_le_iff (x y : ZMod n → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    fourierDistance x y ≤ u ↔ ∀ i, ‖fourierReal x i - fourierReal y i‖ ≤ u := by
  unfold fourierDistance
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hu]
  rfl

lemma norm_fourierReal_le_ellOne (x : ZMod n → ℝ) (k : ZMod n) :
    ‖fourierReal x k‖ ≤ ellOne x := by
  rw [fourierReal_apply, ZMod.dft_apply]
  refine (norm_sum_le _ _).trans_eq ?_
  unfold ellOne
  apply sum_congr rfl
  intro i _
  rw [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

lemma fourierDistance_zero_le (x : ZMod n → ℝ) : fourierDistance x 0 ≤ ellOne x := by
  have hX : 0 ≤ ellOne x := sum_nonneg fun _ _ ↦ abs_nonneg _
  apply (fourierDistance_le_iff _ _ hX).mpr
  intro i
  simpa only [map_zero, Pi.zero_apply, sub_zero] using norm_fourierReal_le_ellOne x i

private abbrev Atom (n : ℕ) := Option (ZMod n × Bool)

private noncomputable def atom (R : ℝ) : Atom n → (ZMod n → ℝ)
  | none => 0
  | some (i, b) => Pi.single i (R * sign b)

private noncomputable def atomWeight (R : ℝ) (x : ZMod n → ℝ) : Atom n → ℝ
  | none => 1 - ellOne x / R
  | some (i, b) => max (sign b * x i) 0 / R

private lemma atom_ellOne_le {R : ℝ} (hR : 0 ≤ R) (a : Atom n) : ellOne (atom R a) ≤ R := by
  cases a with
  | none => simp [ellOne, atom, hR]
  | some z =>
    obtain ⟨i, b⟩ := z
    simp only [ellOne, atom, Pi.single_apply]
    simp [apply_ite, abs_mul, abs_of_nonneg hR]

private lemma atomWeight_nonneg {R : ℝ} (hR : 0 < R) (x : ZMod n → ℝ)
    (hx : ellOne x ≤ R) (a : Atom n) : 0 ≤ atomWeight R x a := by
  cases a with
  | none =>
    simp only [atomWeight, sub_nonneg]
    exact (div_le_iff₀ hR).2 (by simpa only [one_mul] using hx)
  | some z =>
    obtain ⟨i, b⟩ := z
    exact div_nonneg (le_max_right _ _) hR.le

private lemma sum_atomWeight {R : ℝ} (x : ZMod n → ℝ) :
    (∑ a : Atom n, atomWeight R x a) = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have h (i : ZMod n) : (∑ b : Bool, atomWeight R x (some (i, b))) = |x i| / R := by
    simp only [Fintype.sum_bool, atomWeight, sign_false, sign_true, neg_one_mul, one_mul, ← add_div]
    congr 1
    by_cases h : 0 ≤ x i
    · simp [h, neg_nonpos.mpr h, abs_of_nonneg h]
    · have h' : x i ≤ 0 := le_of_not_ge h
      simp [h', neg_nonneg.mpr h', abs_of_nonpos h']
  simp_rw [h, ← sum_div, atomWeight, ellOne]
  ring

private lemma sum_atomWeight_smul_atom {R : ℝ} (hR : 0 < R) (x : ZMod n → ℝ) :
    (∑ a : Atom n, atomWeight R x a • atom R a) = x := by
  funext j
  simp only [Fintype.sum_apply, Fintype.sum_option, Fintype.sum_prod_type]
  have h (i : ZMod n) : (∑ b : Bool, (atomWeight R x (some (i, b)) • atom R (some (i, b))) j) =
      if i = j then x j else 0 := by
    by_cases hij : i = j
    · subst i
      simp only [Fintype.sum_bool, atomWeight, atom, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        sign_false, sign_true, neg_one_mul, one_mul, mul_neg, ite_true]
      by_cases h : 0 ≤ x j
      · simp [h, neg_nonpos.mpr h, hR.ne']
      · have h' : x j ≤ 0 := le_of_not_ge h
        simp [h', neg_nonneg.mpr h', hR.ne']
    · simp [atom, hij, Ne.symm hij]
  simp_rw [h]
  simp [atom]

private noncomputable def empiricalAtomMean (R : ℝ) {m : ℕ} (w : Fin m → Atom n) :
    ZMod n → ℝ :=
  (m : ℝ)⁻¹ • ∑ i, atom R (w i)

private lemma fourier_empiricalAtomMean (R : ℝ) {m : ℕ} (w : Fin m → Atom n) (k : ZMod n) :
    fourierReal (empiricalAtomMean R w) k =
      (∑ j, fourierReal (atom R (w j)) k) / (m : ℂ) := by
  simp [empiricalAtomMean, map_sum, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

private lemma exists_empiricalAtomMean_close {R u : ℝ} (hR : 0 < R) (hu : 0 < u)
    (x : ZMod n → ℝ) (hx : ellOne x ≤ R) {m : ℕ} (hm : 0 < m)
    (hTail : 4 * n * Real.exp (-(m : ℝ) * u ^ 2 / (32 * R ^ 2)) < 1) :
    ∃ w : Fin m → Atom n, fourierDistance (empiricalAtomMean R w) x ≤ u / 2 := by
  let : MeasurableSpace (Atom n) := ⊤
  let : MeasurableSingletonClass (Atom n) := ⟨fun _ ↦ trivial⟩
  have hPsum : (∑ a : Atom n, ENNReal.ofReal (atomWeight R x a)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ atomWeight_nonneg hR x hx a),
      sum_atomWeight, ENNReal.ofReal_one]
  let p := PMF.ofFintype (fun a : Atom n ↦ ENNReal.ofReal (atomWeight R x a)) hPsum
  let f (a : Atom n) (k : ZMod n) := fourierReal (atom R a) k
  have hMean : (∑ a : Atom n, atomWeight R x a • fourierReal (atom R a : ZMod n → ℝ)) =
      fourierReal x := by
    simp_rw [← map_smul, ← map_sum, sum_atomWeight_smul_atom hR]
  have hMeanRe (k : ZMod n) : (∫ a, (f a k).re ∂p.toMeasure) = (fourierReal x k).re := by
    rw [PMF.integral_eq_sum]
    have h := congrArg (fun y : ZMod n → ℂ ↦ (y k).re) hMean
    change ((∑ a : Atom n, atomWeight R x a • fourierReal (atom R a)) k).re =
      (fourierReal x k).re at h
    simp only [Fintype.sum_apply, Complex.re_sum, Pi.smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    simpa only [p, PMF.ofFintype_apply, ENNReal.toReal_ofReal (atomWeight_nonneg hR x hx _),
      smul_eq_mul, f] using h
  have hMeanIm (k : ZMod n) : (∫ a, (f a k).im ∂p.toMeasure) = (fourierReal x k).im := by
    rw [PMF.integral_eq_sum]
    have h := congrArg (fun y : ZMod n → ℂ ↦ (y k).im) hMean
    change ((∑ a : Atom n, atomWeight R x a • fourierReal (atom R a)) k).im =
      (fourierReal x k).im at h
    simp only [Fintype.sum_apply, Complex.im_sum, Pi.smul_apply, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
    simpa only [p, PMF.ofFintype_apply, ENNReal.toReal_ofReal (atomWeight_nonneg hR x hx _),
      smul_eq_mul, f] using h
  obtain ⟨w, hw⟩ := exists_empirical_mean (μ := p.toMeasure) f (fourierReal x)
    (fun _ ↦ measurable_of_countable _) (fun _ ↦ measurable_of_countable _)
    hMeanRe hMeanIm hR hu
    (fun a k ↦ (norm_fourierReal_le_ellOne (atom R a) k).trans (atom_ellOne_le hR.le a)) hm
    (by simpa only [ZMod.card] using hTail)
  refine ⟨w, (fourierDistance_le_iff _ _ (by positivity)).mpr fun k ↦ ?_⟩
  simpa only [fourier_empiricalAtomMean, f] using hw k

/-- A Fourier net contained in a subset of the real ℓ¹ ball. The cardinality
bound counts ordered samples of the zero and signed coordinate atoms. -/
theorem exists_fourier_net (A : Set (ZMod n → ℝ)) {R u : ℝ} (hR : 0 < R) (hu : 0 < u)
    (hA : ∀ x ∈ A, ellOne x ≤ R) {m : ℕ} (hm : 0 < m)
    (hTail : 4 * n * Real.exp (-(m : ℝ) * u ^ 2 / (32 * R ^ 2)) < 1) :
    ∃ S : Finset (ZMod n → ℝ), ↑S ⊆ A ∧ S.card ≤ (2 * n + 1) ^ m ∧
      ∀ x ∈ A, ∃ y ∈ S, fourierDistance x y ≤ u := by
  classical
  let Sample := {w : Fin m → Atom n // ∃ x ∈ A, fourierDistance (empiricalAtomMean R w) x ≤ u / 2}
  let representative (w : Sample) := w.property.choose
  let S := (univ : Finset Sample).image representative
  refine ⟨S, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨w, _, rfl⟩ := mem_image.mp hy
    exact w.property.choose_spec.1
  · have hCard : S.card ≤ Fintype.card (Fin m → Atom n) := by
      exact card_image_le.trans ((card_univ (α := Sample)).trans_le
        (Fintype.card_le_of_injective Subtype.val Subtype.val_injective))
    simpa [Fintype.card_fun, Fintype.card_option, Fintype.card_prod, ZMod.card, mul_comm] using hCard
  · intro x hx
    obtain ⟨w, hw⟩ := exists_empiricalAtomMean_close hR hu x (hA x hx) hm hTail
    let a : Sample := ⟨w, x, hx, hw⟩
    refine ⟨representative a, mem_image.mpr ⟨a, mem_univ a, rfl⟩, ?_⟩
    have hd := a.property.choose_spec.2
    change fourierDistance (empiricalAtomMean R w) (representative a) ≤ u / 2 at hd
    have ht := fourierDistance_triangle x (empiricalAtomMean R w) (representative a)
    rw [fourierDistance_comm x (empiricalAtomMean R w)] at ht
    linarith

end LovaszTheta.Circulant
