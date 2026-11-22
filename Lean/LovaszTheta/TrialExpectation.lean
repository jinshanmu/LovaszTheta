module

public import LovaszTheta.KernelBound

/-!
# Passing from a trial residual to the normalized expectation

On the Fourier kernel event, the discrepancy is controlled by the
Euclidean trial norm times the residual, plus the bound on the exact
solution times the residual. The first and second moments needed for
the expectation estimate are explicit.
-/

@[expose] public section

open Finset
open scoped Classical Matrix

namespace LovaszTheta.Circulant

private lemma average_mul_le_sqrt {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) :
    average (fun x ↦ a x * b x) ≤
      Real.sqrt (average fun x ↦ a x ^ 2) * Real.sqrt (average fun x ↦ b x ^ 2) := by
  have hc : 0 ≤ (Fintype.card Ω : ℝ) := by positivity
  have ha : 0 ≤ ∑ x, a x ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hb : 0 ≤ ∑ x, b x ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold average
  rw [Real.sqrt_div ha, Real.sqrt_div hb, div_mul_div_comm, Real.mul_self_sqrt hc]
  apply div_le_div_of_nonneg_right _ hc
  have h := (le_abs_self (a ⬝ᵥ b)).trans (abs_dotProduct_le a b)
  simpa only [dotProduct, norm₂, pow_two] using h

private lemma average_le_sqrt {Ω : Type*} [Fintype Ω] [Nonempty Ω] (b : Ω → ℝ) :
    average b ≤ Real.sqrt (average fun x ↦ b x ^ 2) := by
  simpa only [one_mul, one_pow, average_const, Real.sqrt_one] using
    (average_mul_le_sqrt (fun _ : Ω ↦ 1) b)

variable {n : ℕ} [NeZero n]

/-- Normalized theta expectation in terms of the trial norm, its zero
coordinate and its residual. -/
theorem expectedTheta_div_sqrt_le_of_trial (hn : 1 < n) {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (v : (InversionClass n → Bool) → ZMod n → ℝ) :
    let A := average (fun x ↦ norm₂ (v x) ^ 2)
    let B := average (fun x ↦ norm₂ (v x - signOperator x (smooth (weight n τ) (v x))) ^ 2)
    let C := average (fun x ↦ (v x 0) ^ 2)
    expectedTheta n / Real.sqrt n ≤
      Real.sqrt (1 + τ) * Real.exp (3 * δ / 2) +
      ((1 + 4 * Real.sqrt (n * Real.log n)) / Real.sqrt n) *
        (4 * Real.exp (-(kernelLog n ^ 2)) + C / δ ^ 2 +
          (Real.sqrt A + 65536 * Real.sqrt (1 + τ) * kernelLog n ^ 2) * Real.sqrt B / δ ^ 2) +
      Real.sqrt n * (2 * (n : ℝ)⁻¹ ^ 3) := by
  let Ω := InversionClass n → Bool
  let a (x : Ω) := norm₂ (v x)
  let b (x : Ω) := norm₂ (v x - signOperator x (smooth (weight n τ) (v x)))
  let A := average (fun x ↦ a x ^ 2)
  let B := average (fun x ↦ b x ^ 2)
  let C := average (fun x ↦ (v x 0) ^ 2)
  let R := 65536 * Real.sqrt (1 + τ) * kernelLog n ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  choose p hp q hq hPos hpM hqM hFixed hUpper using
    fun x : Ω ↦ exists_smoothed_factors x hτ
  let Δ (x : Ω) := discrepancy (weight n τ) (p x) (v x)
  let E (x : Ω) := if kernelControl x then Δ x else 0
  have hBounds (x : Ω) := theta_residual_bound_of_factors x hτ (hPos x)
    (hpM x) (hqM x) (hFixed x) (hUpper x) (v x)
  have hDelta (x : Ω) : 0 ≤ E x := by
    dsimp only [E]
    split_ifs
    · exact (hBounds x).1
    · exact le_rfl
  have hE : average E ≤ (Real.sqrt A + R) * Real.sqrt B := by
    calc
      _ ≤ average (fun x ↦ (a x + R) * b x) := by
        apply average_mono
        intro x
        by_cases hx : kernelControl x
        · have hF := norm₂_factor_sub_le hn.le x hx hτ (hp x) (hq x)
            (fun i ↦ ⟨(hPos x i).1.le, (hPos x i).2.1.le⟩) (hpM x) (hqM x)
          have hHalf : norm₂ (p x - q x) / 2 ≤ R := by dsimp [R]; linarith
          unfold E
          rw [ite_eq_left hx]
          exact (hBounds x).2.1.trans
            (mul_le_mul_of_nonneg_right (add_le_add (le_refl (a x)) hHalf) (norm₂_nonneg _))
        · simpa only [E, hx, ite_false] using
            mul_nonneg (add_nonneg (norm₂_nonneg _) hR) (norm₂_nonneg _)
      _ = average (fun x ↦ a x * b x) + R * average b := by
        simp_rw [add_mul, average_add, average_mul_left]
      _ ≤ _ := by
        rw [add_mul]
        exact add_le_add (average_mul_le_sqrt a b) (mul_le_mul_of_nonneg_left (average_le_sqrt b) hR)
  let good (x : Ω) := kernelControl x ∧ |v x 0| ≤ δ ∧ Δ x ≤ δ ^ 2
  let badK (x : Ω) := ¬kernelControl x
  let badV (x : Ω) := δ ^ 2 ≤ (v x 0) ^ 2
  let badD (x : Ω) := δ ^ 2 ≤ E x
  have hFail (x : Ω) (hx : ¬good x) : badK x ∨ badV x ∨ badD x := by
    by_cases hk : kernelControl x
    · by_cases hv : |v x 0| ≤ δ
      · have hD : δ ^ 2 ≤ Δ x := (lt_of_not_ge fun h ↦ hx ⟨hk, hv, h⟩).le
        exact Or.inr (Or.inr (by simpa only [badD, E, hk, ite_true] using hD))
      · have h : δ ^ 2 ≤ |v x 0| ^ 2 :=
          pow_le_pow_left₀ hδ.le (le_of_lt (lt_of_not_ge hv)) _
        exact Or.inr (Or.inl (by simpa only [badV, sq_abs] using h))
    · exact Or.inl hk
  have hP : probability (fun x ↦ ¬good x) ≤
      4 * Real.exp (-(kernelLog n ^ 2)) + C / δ ^ 2 +
        (Real.sqrt A + R) * Real.sqrt B / δ ^ 2 := by
    have hKP : probability badK ≤ 4 * Real.exp (-(kernelLog n ^ 2)) :=
      probability_kernelControl_failure hn.le
    have hVP : probability badV ≤ C / δ ^ 2 :=
      probability_le_average_div _ (sq_pos_of_pos hδ) (fun _ ↦ sq_nonneg _)
    have hDP : probability badD ≤ (Real.sqrt A + R) * Real.sqrt B / δ ^ 2 :=
      (probability_le_average_div E (sq_pos_of_pos hδ) hDelta).trans
        (div_le_div_of_nonneg_right hE (sq_nonneg δ))
    calc
      _ ≤ probability (fun x ↦ badK x ∨ badV x ∨ badD x) := probability_mono hFail
      _ ≤ probability badK + probability (fun x ↦ badV x ∨ badD x) := probability_le_add _ _
      _ ≤ probability badK + (probability badV + probability badD) :=
        add_le_add (le_refl (probability badK)) (probability_le_add badV badD)
      _ ≤ _ := by rw [← add_assoc]; exact add_le_add (add_le_add hKP hVP) hDP
  have hGood (x : Ω) (hx : good x) :
      theta (graph x) / Real.sqrt n ≤ Real.sqrt (1 + τ) * Real.exp (3 * δ / 2) :=
    theta_le_of_log_residual x hτ hδ.le (hBounds x).2.2 hx.2.1 hx.2.2
  have hBound := expectedTheta_div_sqrt_le_of_good hn (by positivity) good hGood
  have hS : 0 ≤ ((1 + 4 * Real.sqrt (n * Real.log n)) / Real.sqrt n) := by positivity
  exact hBound.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hP hS)) le_rfl)

end LovaszTheta.Circulant
