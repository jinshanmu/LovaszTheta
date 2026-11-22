module

public import LovaszTheta.Smoothing
public import LovaszTheta.SpectralTail

/-!
# The deterministic and exceptional contributions to the expectation

The residual certificate bounds theta on a good event. The signed
Fourier spectrum controls the contribution of its complement, and the
universal theta bound controls the remaining spectral tail.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

lemma mass_weight_le {τ : ℝ} (hτ : 0 ≤ τ) : mass (weight n τ) ≤ 1 + τ := by
  classical
  let s := (univ : Finset (ZMod n)).erase 0
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hCard : (s.card : ℝ) ≤ n := by
    have h := Finset.card_le_card (erase_subset (0 : ZMod n) (univ : Finset (ZMod n)))
    rw [card_univ, ZMod.card] at h
    exact_mod_cast h
  have hSum : (∑ i ∈ s, weight n τ i) = ∑ _i ∈ s, τ / n :=
    sum_congr rfl fun i hi ↦ by simp [weight, (mem_erase.mp hi).1]
  unfold mass
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))]
  change (∑ i ∈ s, weight n τ i) + weight n τ 0 ≤ _
  rw [hSum, sum_const, nsmul_eq_mul, weight_zero]
  have h := mul_le_mul_of_nonneg_right hCard (div_nonneg hτ hn.le)
  rw [mul_div_cancel₀ (by exact hn.ne') (a := τ)] at h
  linarith

/-- The pointwise upper bound on the event where the trial zero
coordinate and the discrepancy have the specified sizes. -/
theorem theta_le_of_log_residual (x : InversionClass n → Bool) {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 ≤ δ) {p v : ZMod n → ℝ}
    (hLog : Real.log (theta (graph x) / Real.sqrt n) ≤
      Real.log (mass (weight n τ)) / 2 + |v 0| / 2 +
        Real.sqrt (discrepancy (weight n τ) p v))
    (hv : |v 0| ≤ δ) (hD : discrepancy (weight n τ) p v ≤ δ ^ 2) :
    theta (graph x) / Real.sqrt n ≤ Real.sqrt (1 + τ) * Real.exp (3 * δ / 2) := by
  have hΘ : 0 < theta (graph x) / Real.sqrt n :=
    div_pos (zero_lt_one.trans_le (one_le_theta _))
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)))
  have hS : Real.sqrt (discrepancy (weight n τ) p v) ≤ δ :=
    Real.sqrt_le_iff.mpr ⟨hδ, hD⟩
  have hW : 0 < mass (weight n τ) := sum_pos (fun i _ ↦ weight_pos hτ i) univ_nonempty
  have hω := Real.log_le_log hW (mass_weight_le hτ.le)
  have hUp : Real.log (theta (graph x) / Real.sqrt n) ≤
      Real.log (1 + τ) / 2 + 3 * δ / 2 := by linarith
  calc
    _ ≤ Real.exp (Real.log (1 + τ) / 2 + 3 * δ / 2) := (Real.log_le_iff_le_exp hΘ).mp hUp
    _ = _ := by
      rw [Real.exp_add, ← Real.log_sqrt (by linarith : 0 ≤ 1 + τ),
        Real.exp_log (Real.sqrt_pos.mpr (by linarith))]

/-- The finite expectation bound from a pointwise estimate on a good event and
the exceptional-event Fourier tail. -/
theorem expectedTheta_div_sqrt_le_of_good (hn : 1 < n) {a : ℝ} (ha : 0 ≤ a)
    (good : (InversionClass n → Bool) → Prop)
    (hGood : ∀ x, good x → theta (graph x) / Real.sqrt n ≤ a) :
    expectedTheta n / Real.sqrt n ≤
      a + ((1 + 4 * Real.sqrt (n * Real.log n)) / Real.sqrt n) *
        probability (fun x ↦ ¬good x) + Real.sqrt n * (2 * (n : ℝ)⁻¹ ^ 3) := by
  let s := Real.sqrt (n : ℝ)
  let t := 4 * Real.sqrt (n * Real.log n)
  let badSpectrum (x : InversionClass n → Bool) := ∃ k, t ≤ |signedCoefficient x k|
  let indicator (p : (InversionClass n → Bool) → Prop) (x : InversionClass n → Bool) : ℝ :=
    @ite ℝ (p x) (Classical.propDecidable (p x)) 1 0
  have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr (zero_lt_one.trans hn')
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hPoint (x : InversionClass n → Bool) : theta (graph x) / s ≤
      a + (1 + t) / s * indicator (fun z ↦ ¬good z) x + s * indicator badSpectrum x := by
    dsimp only [indicator]
    by_cases hG : good x
    · simp only [hG, not_true_eq_false, ite_false, mul_zero, add_zero]
      have hz : 0 ≤ s * indicator badSpectrum x := by
        dsimp only [indicator]
        split_ifs <;> positivity
      exact (hGood x hG).trans (le_add_of_nonneg_right hz)
    · by_cases hT : badSpectrum x
      · have hTr : theta (graph x) / s ≤ s := by
          apply (div_le_iff₀ hs).mpr
          have h := theta_le_card (graph x)
          simpa only [s, ZMod.card, ← pow_two, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))] using h
        have hz : 0 ≤ a + (1 + t) / s :=
          add_nonneg ha (div_nonneg (add_nonneg zero_le_one ht) hs.le)
        simpa only [hG, not_false_eq_true, hT, ite_true, mul_one] using
          hTr.trans (le_add_of_nonneg_left hz)
      · have hFourier (k : ZMod n) : |signedCoefficient x k| ≤ t :=
          (lt_of_not_ge fun h ↦ hT ⟨k, h⟩).le
        have hLe := div_le_div_of_nonneg_right (theta_le_signedCoefficient x hFourier) hs.le
        simpa only [hG, hT, not_false_eq_true, ite_true, ite_false, mul_one, mul_zero, add_zero] using
          hLe.trans (le_add_of_nonneg_left ha)
  have hE := average_mono hPoint
  rw [average_add, average_add, average_const, average_mul_left, average_mul_left] at hE
  have hL : average (fun (x : InversionClass n → Bool) ↦ theta (graph x) / s) = expectedTheta n / s := by
    simp only [div_eq_inv_mul, average_mul_left, expectedTheta]
  rw [hL] at hE
  change expectedTheta n / s ≤ a + (1 + t) / s * probability (fun x ↦ ¬good x) +
    s * probability badSpectrum at hE
  have hTail : probability badSpectrum ≤ 2 * (n : ℝ)⁻¹ ^ 3 :=
    probability_signedCoefficient_ge_log (n := n) hn
  exact hE.trans (by linarith only [mul_le_mul_of_nonneg_left hTail hs.le])

end LovaszTheta.Circulant
