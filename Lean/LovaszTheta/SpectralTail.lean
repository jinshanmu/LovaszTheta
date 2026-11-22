module

public import LovaszTheta.Program

/-!
# The exceptional-event spectral certificate

The matrix obtained by adding the identity to the signed circulant
agrees with the theta objective on every free entry. Its Fourier
coefficients are real fair-sign sums, with one contribution per
nonzero inversion class, including the singleton if present.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix ZMod Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The real Fourier coefficient of the signed connection function. -/
noncomputable def signedCoefficient (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  (𝓕 (fun s ↦ (epsilon x s : ℂ)) k).re

omit [NeZero n] in
private lemma zero_notMem_inversionClass (c : InversionClass n) : (0 : ZMod n) ∉ c.val := by
  obtain ⟨a, ha, he⟩ := c.property
  rw [he]
  simp [Ne.symm ha, ha]

omit [NeZero n] in
private lemma mem_inversionClass_iff {s : ZMod n} (hs : s ≠ 0) (c : InversionClass n) :
    s ∈ c.val ↔ c = inversionClass s hs := by
  obtain ⟨a, ha, he⟩ := c.property
  have hc : c = inversionClass a ha := Subtype.ext he
  rw [hc, inversionClass_eq_iff ha hs]
  change (s ∈ ({a, -a} : Finset (ZMod n))) ↔ a = s ∨ a = -s
  rw [mem_insert, mem_singleton]
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

/-- Sum over the disjoint partition of the nonzero residues into inversion classes. -/
lemma sum_inversionClass {f : ZMod n → ℝ} (g : InversionClass n → ℝ) :
    (∑ c : InversionClass n, ∑ s ∈ c.val, f s * g c) =
      ∑ s : ZMod n, if hs : s = 0 then 0 else f s * g (inversionClass s hs) := by
  classical
  have h (c : InversionClass n) :
      (∑ s ∈ c.val, f s * g c) = ∑ s : ZMod n, if s ∈ c.val then f s * g c else 0 := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  by_cases hs : s = 0
  · subst s
    simp [zero_notMem_inversionClass]
  · simp only [dite_eq_right hs, mem_inversionClass_iff hs, sum_ite_eq', mem_univ, ite_true]

private noncomputable def classCoefficient (k : ZMod n) (c : InversionClass n) : ℝ :=
  ∑ s ∈ c.val, (ZMod.stdAddChar (-(s * k))).re

private lemma signedCoefficient_eq_sum (x : InversionClass n → Bool) (k : ZMod n) :
    signedCoefficient x k = ∑ c, classCoefficient k c * sign (x c) := by
  unfold signedCoefficient classCoefficient
  simp only [ZMod.dft_apply, smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, sum_mul]
  rw [sum_inversionClass]
  exact sum_congr rfl fun s _ ↦ by
    by_cases hs : s = 0 <;> simp [epsilon, hs]

private lemma sum_sq_classCoefficient_le (k : ZMod n) :
    (∑ c, classCoefficient k c ^ 2) ≤ 2 * (n : ℝ) := by
  have hNorm (s : ZMod n) : |(ZMod.stdAddChar (-(s * k))).re| ≤ 1 := by
    apply (Complex.abs_re_le_norm _).trans_eq
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  have hClass (c : InversionClass n) :
      classCoefficient k c ^ 2 ≤ 2 * (c.val.card : ℝ) := by
    have hc : (c.val.card : ℝ) ≤ 2 := by exact_mod_cast inversionClass_card_le c
    calc
      _ ≤ (c.val.card : ℝ) * ∑ s ∈ c.val, (ZMod.stdAddChar (-(s * k))).re ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ (c.val.card : ℝ) * ∑ _s ∈ c.val, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun s _ ↦ by
          have hs : |(ZMod.stdAddChar (-(s * k))).re| ≤ |(1 : ℝ)| := by
            simpa only [abs_one] using hNorm s
          simpa only [one_pow] using sq_le_sq.mpr hs) (by positivity)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hSizes : (∑ c : InversionClass n, (c.val.card : ℝ)) ≤ n := by
    calc
      _ = ∑ c : InversionClass n, ∑ _s ∈ c.val, (1 : ℝ) := by simp
      _ = ∑ s : ZMod n, if s = 0 then (0 : ℝ) else 1 := by
        simpa only [mul_one, dite_eq_ite] using
          (sum_inversionClass (f := fun _ ↦ 1) (fun _ ↦ 1))
      _ ≤ ∑ _s : ZMod n, (1 : ℝ) := sum_le_sum fun s _ ↦ by split_ifs <;> norm_num
      _ = _ := by simp [ZMod.card]
  calc
    _ ≤ ∑ c : InversionClass n, 2 * (c.val.card : ℝ) := sum_le_sum fun c _ ↦ hClass c
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hSizes (by norm_num)

omit [NeZero n] in
private lemma epsilon_eq_one_of_nonedge (x : InversionClass n → Bool) {i j : ZMod n}
    (hne : i ≠ j) (h : ¬(graph x).Adj i j) : epsilon x (i - j) = 1 := by
  have hne' : i - j ≠ 0 := sub_ne_zero.mpr hne
  rw [graph_adj_iff_epsilon] at h
  cases hx : x (inversionClass (i - j) hne')
  · exfalso
    exact h (by simp [epsilon, hne', hx])
  · simp [epsilon, hne', hx]

/-- The deterministic signed-circulant certificate from the expectation bound. -/
theorem theta_le_signedCoefficient (x : InversionClass n → Bool) {c : ℝ}
    (h : ∀ k, |signedCoefficient x k| ≤ c) : theta (graph x) ≤ 1 + c := by
  let B : Matrix (ZMod n) (ZMod n) ℝ := 1 + Matrix.circulant (epsilon x)
  refine theta_le_of_majorant (B := B) ?_ ?_
  · let z₀ : ZMod n → ℝ := fun s ↦ if s = 0 then c else 0
    let z := z₀ - epsilon x
    have hz₀ : z₀.Even := by intro s; simp [z₀]
    have hz : z.Even := fun s ↦ by simp only [z, Pi.sub_apply, hz₀ s, epsilon_even x s]
    have hMat : (1 + c) • (1 : Matrix (ZMod n) (ZMod n) ℝ) - B = Matrix.circulant z := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [B, z, z₀, Matrix.circulant_apply]
      · simp [B, z, z₀, Matrix.circulant_apply, Matrix.one_apply_ne hij, sub_ne_zero.mpr hij]
    rw [hMat, circulant_psd_iff_dft_nonneg hz]
    intro k
    have hDft₀ : 𝓕 (fun s ↦ (z₀ s : ℂ)) k = (c : ℂ) := by
      rw [ZMod.dft_apply]
      simp [z₀, apply_ite, Finset.sum_ite_eq']
    have hDft : (fun s ↦ (z s : ℂ)) =
        (fun s ↦ (z₀ s : ℂ)) - (fun s ↦ (epsilon x s : ℂ)) := by
      funext s
      simp [z]
    rw [hDft, map_sub]
    change 0 ≤ (𝓕 (fun s ↦ (z₀ s : ℂ)) k - 𝓕 (fun s ↦ (epsilon x s : ℂ)) k).re
    rw [Complex.sub_re, hDft₀, Complex.ofReal_re]
    exact sub_nonneg.mpr ((le_abs_self (signedCoefficient x k)).trans (h k))
  · intro i j hij
    by_cases he : i = j
    · subst j
      simp [B, Matrix.circulant_apply]
    · simp [B, Matrix.circulant_apply, Matrix.one_apply_ne he,
        epsilon_eq_one_of_nonedge x he hij]

/-- The tail bound after taking the union over the Fourier frequencies. -/
theorem probability_signedCoefficient_ge {t : ℝ} (ht : 0 < t) :
    probability (fun (x : InversionClass n → Bool) ↦ ∃ k, t ≤ |signedCoefficient x k|) ≤
      2 * n * Real.exp (-(t ^ 2) / (4 * n)) := by
  classical
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hSingle (k : ZMod n) :
      probability (fun (x : InversionClass n → Bool) ↦ t ≤ |signedCoefficient x k|) ≤
        2 * Real.exp (-(t ^ 2) / (4 * n)) := by
    simp_rw [signedCoefficient_eq_sum]
    simpa only [show (2 : ℝ) * (2 * n) = 4 * n by ring] using
      probability_abs_signSum_ge (classCoefficient k) ht (by positivity : 0 < 2 * (n : ℝ))
        (sum_sq_classCoefficient_le k)
  calc
    _ ≤ ∑ k : ZMod n, probability (fun (x : InversionClass n → Bool) ↦ t ≤ |signedCoefficient x k|) :=
      probability_exists_le_sum _
    _ ≤ ∑ _k : ZMod n, 2 * Real.exp (-(t ^ 2) / (4 * n)) :=
      sum_le_sum fun k _ ↦ hSingle k
    _ = _ := by simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; ring

/-- The exceptional-event threshold and probability in the manuscript. -/
theorem probability_signedCoefficient_ge_log (hn : 1 < n) :
    probability (fun (x : InversionClass n → Bool) ↦
      ∃ k, 4 * Real.sqrt (n * Real.log n) ≤ |signedCoefficient x k|) ≤
      2 * (n : ℝ)⁻¹ ^ 3 := by
  have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
  have hPos : 0 < (n : ℝ) := zero_lt_one.trans hn'
  have hLog : 0 < Real.log n := Real.log_pos hn'
  have hThreshold : 0 < 4 * Real.sqrt (n * Real.log n) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hPos hLog))
  refine (probability_signedCoefficient_ge hThreshold).trans_eq ?_
  rw [mul_pow, Real.sq_sqrt (mul_pos hPos hLog).le]
  have hExp : -((4 : ℝ) ^ 2 * (n * Real.log n)) / (4 * n) = -(4 * Real.log n) := by
    field_simp
  rw [hExp, Real.exp_neg, show (4 : ℝ) * Real.log n = (4 : ℕ) * Real.log n by norm_num,
    Real.exp_nat_mul, Real.exp_log hPos]
  field_simp

end LovaszTheta.Circulant
