module

public import LovaszTheta.SpectralTail

/-!
# Increments of the Fourier kernel process

This proves the Parseval and fair-sign increment estimates used before
the net construction in the Fourier kernel bound.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- Parseval's formula with the unnormalized discrete Fourier transform. -/
theorem sum_norm_dft_sq (x : ZMod n → ℂ) :
    (∑ k, ‖𝓕 x k‖ ^ 2) = (n : ℝ) * ∑ k, ‖x k‖ ^ 2 := by
  let F := fourierMatrix n
  have hDot : star (F *ᵥ x) ⬝ᵥ (F *ᵥ x) = (n : ℂ) * (star x ⬝ᵥ x) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    change star x ⬝ᵥ ((fourierMatrix n)ᴴ * fourierMatrix n) *ᵥ x = _
    rw [fourierMatrix_conjTranspose_mul, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hDotNorm (v : ZMod n → ℂ) : star v ⬝ᵥ v = ∑ k, (‖v k‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_sum]
    simp only [dotProduct, Pi.star_apply, Complex.star_def]
    exact sum_congr rfl fun k _ ↦ by rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  rw [hDotNorm, hDotNorm] at hDot
  have hDFT : F *ᵥ x = 𝓕 x := fourierMatrix_mulVec x
  rw [hDFT, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hDot
  exact Complex.ofReal_injective hDot

/-- The Rademacher quadratic process from the Fourier kernel argument. -/
noncomputable def kernelProcess (signs : InversionClass n → Bool) (x : ZMod n → ℂ) : ℝ :=
  (∑ s, epsilon signs s * ‖𝓕 x s‖ ^ 2) / n

private noncomputable def normSum (x y : ZMod n → ℂ) (s : ZMod n) : ℝ :=
  ‖𝓕 x s‖ + ‖𝓕 y s‖

private noncomputable def normDifferenceSq (x y : ZMod n → ℂ) (s : ZMod n) : ℝ :=
  ‖𝓕 x s‖ ^ 2 - ‖𝓕 y s‖ ^ 2

private lemma abs_normDifferenceSq_le (x y : ZMod n → ℂ) {d : ℝ}
    (hd : ∀ s, ‖𝓕 x s - 𝓕 y s‖ ≤ d) (s : ZMod n) :
    |normDifferenceSq x y s| ≤ d * normSum x y s := by
  have hNonneg : 0 ≤ normSum x y s := add_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [normDifferenceSq, sq_sub_sq, abs_mul]
  change |normSum x y s| * |‖𝓕 x s‖ - ‖𝓕 y s‖| ≤ _
  rw [abs_of_nonneg hNonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans (hd s)) hNonneg

private lemma sum_normSum_sq_le (x y : ZMod n → ℂ)
    (hx : ∑ s, ‖x s‖ ^ 2 ≤ 1) (hy : ∑ s, ‖y s‖ ^ 2 ≤ 1) :
    (∑ s, normSum x y s ^ 2) ≤ 4 * n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hx' := mul_le_mul_of_nonneg_left hx hn
  have hy' := mul_le_mul_of_nonneg_left hy hn
  calc
    _ ≤ ∑ s, 2 * (‖𝓕 x s‖ ^ 2 + ‖𝓕 y s‖ ^ 2) := sum_le_sum fun s _ ↦ by
      dsimp [normSum]
      nlinarith [sq_nonneg (‖𝓕 x s‖ - ‖𝓕 y s‖)]
    _ ≤ _ := by
      rw [← mul_sum, sum_add_distrib, sum_norm_dft_sq, sum_norm_dft_sq]
      linarith

private lemma sum_normSum_le (x y : ZMod n → ℂ)
    (hx : ∑ s, ‖x s‖ ^ 2 ≤ 1) (hy : ∑ s, ‖y s‖ ^ 2 ≤ 1) :
    (∑ s, normSum x y s) ≤ 2 * n := by
  have h (z : ZMod n → ℂ) (hz : ∑ s, ‖z s‖ ^ 2 ≤ 1) : (∑ s, ‖𝓕 z s‖) ≤ n := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hz' := mul_le_mul_of_nonneg_left hz hn
    calc
      _ ≤ ∑ s : ZMod n, (‖𝓕 z s‖ ^ 2 + 1) / 2 :=
        sum_le_sum fun s _ ↦ by nlinarith [sq_nonneg (‖𝓕 z s‖ - 1)]
      _ ≤ _ := by
        rw [← sum_div, sum_add_distrib, sum_norm_dft_sq]
        simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at *
        linarith
  unfold normSum
  rw [sum_add_distrib]
  linarith [h x hx, h y hy]

omit [NeZero n] in
private lemma abs_epsilon_le_one (signs : InversionClass n → Bool) (s : ZMod n) :
    |epsilon signs s| ≤ 1 := by
  by_cases hs : s = 0 <;> simp [epsilon, hs]

/-- The deterministic Lipschitz estimate for increments in Fourier sup distance. -/
theorem abs_kernelProcess_sub_le (signs : InversionClass n → Bool) (x y : ZMod n → ℂ)
    (hx : ∑ s, ‖x s‖ ^ 2 ≤ 1) (hy : ∑ s, ‖y s‖ ^ 2 ≤ 1) {d : ℝ} (hd₀ : 0 ≤ d)
    (hd : ∀ s, ‖𝓕 x s - 𝓕 y s‖ ≤ d) :
    |kernelProcess signs x - kernelProcess signs y| ≤ 2 * d := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold kernelProcess
  rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).mpr
  simp_rw [← mul_sub]
  change |∑ s, epsilon signs s * normDifferenceSq x y s| ≤ _
  calc
    _ ≤ ∑ s, |epsilon signs s * normDifferenceSq x y s| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, d * normSum x y s := sum_le_sum fun s _ ↦ by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_epsilon_le_one signs s)).trans
        (abs_normDifferenceSq_le x y hd s)
    _ ≤ _ := by
      rw [← mul_sum]
      have hSum := mul_le_mul_of_nonneg_left (sum_normSum_le x y hx hy) hd₀
      linarith

private noncomputable def incrementCoefficient (x y : ZMod n → ℂ) (c : InversionClass n) : ℝ :=
  (∑ s ∈ c.val, normDifferenceSq x y s) / n

private lemma kernelProcess_sub_eq_sum (signs : InversionClass n → Bool) (x y : ZMod n → ℂ) :
    kernelProcess signs x - kernelProcess signs y =
      ∑ c, incrementCoefficient x y c * sign (signs c) := by
  unfold kernelProcess incrementCoefficient
  rw [← sub_div, ← sum_sub_distrib]
  simp only [← mul_sub, div_mul_eq_mul_div, ← sum_div, sum_mul]
  rw [sum_inversionClass]
  congr 1
  apply sum_congr rfl
  intro s _
  by_cases hs : s = 0 <;> simp [epsilon, hs, mul_comm, normDifferenceSq]

private lemma sum_incrementCoefficient_sq_le (x y : ZMod n → ℂ)
    (hx : ∑ s, ‖x s‖ ^ 2 ≤ 1) (hy : ∑ s, ‖y s‖ ^ 2 ≤ 1) {d : ℝ} (hd₀ : 0 ≤ d)
    (hd : ∀ s, ‖𝓕 x s - 𝓕 y s‖ ≤ d) :
    (∑ c, incrementCoefficient x y c ^ 2) ≤ 8 * d ^ 2 / n := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hSq (s : ZMod n) : normDifferenceSq x y s ^ 2 ≤ d ^ 2 * normSum x y s ^ 2 := by
    have hz : 0 ≤ normSum x y s := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hNonneg : 0 ≤ d * normSum x y s := mul_nonneg hd₀ hz
    rw [← mul_pow, sq_le_sq, abs_of_nonneg hNonneg]
    exact abs_normDifferenceSq_le x y hd s
  have hClass (c : InversionClass n) :
      incrementCoefficient x y c ^ 2 ≤
        2 * (∑ s ∈ c.val, d ^ 2 * normSum x y s ^ 2) / (n : ℝ) ^ 2 := by
    rw [incrementCoefficient, div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hCard : (c.val.card : ℝ) ≤ 2 := by exact_mod_cast inversionClass_card_le c
    calc
      _ ≤ (c.val.card : ℝ) * ∑ s ∈ c.val, normDifferenceSq x y s ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ 2 * ∑ s ∈ c.val, normDifferenceSq x y s ^ 2 :=
        mul_le_mul_of_nonneg_right hCard (sum_nonneg fun s _ ↦ sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun s _ ↦ hSq s) (by norm_num)
  have hPartition :
      (∑ c : InversionClass n, ∑ s ∈ c.val, d ^ 2 * normSum x y s ^ 2) ≤
        ∑ s : ZMod n, d ^ 2 * normSum x y s ^ 2 := by
    have h := sum_inversionClass (f := fun s ↦ d ^ 2 * normSum x y s ^ 2) (fun _ ↦ 1)
    simp only [mul_one, dite_eq_ite] at h
    rw [h]
    apply sum_le_sum
    intro s _
    split_ifs
    · positivity
    · exact le_rfl
  calc
    _ ≤ ∑ c, 2 * (∑ s ∈ c.val, d ^ 2 * normSum x y s ^ 2) / (n : ℝ) ^ 2 :=
      sum_le_sum fun c _ ↦ hClass c
    _ ≤ 2 * (∑ s, d ^ 2 * normSum x y s ^ 2) / (n : ℝ) ^ 2 := by
      rw [← sum_div, ← mul_sum]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPartition (by norm_num)) (sq_nonneg _)
    _ ≤ 2 * (d ^ 2 * (4 * n)) / (n : ℝ) ^ 2 := by
      rw [← mul_sum]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_normSum_sq_le x y hx hy)
          (sq_nonneg _)) (by norm_num)) (sq_nonneg _)
    _ = _ := by
      field_simp
      ring

/-- The sign-fluctuation estimate for one increment of the Fourier kernel process. -/
theorem probability_kernelProcess_sub_ge (x y : ZMod n → ℂ) (hx : ∑ s, ‖x s‖ ^ 2 ≤ 1)
    (hy : ∑ s, ‖y s‖ ^ 2 ≤ 1) {d t : ℝ} (hd₀ : 0 < d) (ht : 0 < t)
    (hd : ∀ s, ‖𝓕 x s - 𝓕 y s‖ ≤ d) :
    probability (fun signs ↦ t ≤ |kernelProcess signs x - kernelProcess signs y|) ≤
      2 * Real.exp (-(t ^ 2) / (16 * d ^ 2 / n)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  simp_rw [kernelProcess_sub_eq_sum]
  have hBound := probability_abs_signSum_ge (incrementCoefficient x y) ht
    (by positivity : 0 < 8 * d ^ 2 / (n : ℝ)) (sum_incrementCoefficient_sq_le x y hx hy hd₀.le hd)
  convert hBound using 3
  ring

end LovaszTheta.Circulant
