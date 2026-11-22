module

public import LovaszTheta.FiniteMoments
public import Mathlib.Analysis.MeanInequalities

/-!
# Hölder's inequality for the three sign differences

A product of three sign differences uses three sixth moments
and the growth bound for the derivative uses a second moment.
-/

@[expose] public section

open Finset

namespace LovaszTheta.Circulant

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

private lemma abs_pow_six (x : ℝ) : |x|^6 = x^6 := by
  rw [show (6 : ℕ) = 2*3 by decide, pow_mul, sq_abs, ← pow_mul]

/-- Hölder with sixth moments for one factor and two copies of another. -/
theorem l2Average_mul_sq_le_of_six (f g : Ω → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : average (fun x ↦ f x ^ 6) ≤ A^6) (hg : average (fun x ↦ g x ^ 6) ≤ B^6) :
    l2Average (fun x ↦ |f x| * |g x|^2) ≤ A * B^2 := by
  let N := (Fintype.card Ω : ℝ)
  have hN : 0 < N := by unfold N; exact_mod_cast (Fintype.card_pos (α := Ω))
  have hF : (∑ x, f x ^ 6) ≤ N * A^6 := by
    unfold average at hf
    simpa only [mul_comm] using (div_le_iff₀ hN).mp hf
  have hG : (∑ x, g x ^ 6) ≤ N * B^6 := by
    unfold average at hg
    simpa only [mul_comm] using (div_le_iff₀ hN).mp hg
  have hH : Real.HolderTriple 6 3 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h := Real.Lr_rpow_le_Lp_mul_Lq univ f (fun x ↦ (g x)^2) hH
  have hG' (x : Ω) : |g x^2|^3 = g x^6 := by
    rw [abs_of_nonneg (sq_nonneg _), ← pow_mul]
  simp only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, hG', abs_pow_six] at h
  have hAlg :
      (N*A^6)^(2/6 : ℝ) * (N*B^6)^(2/3 : ℝ) = N * (A * B^2)^2 := by
    rw [Real.mul_rpow hN.le (pow_nonneg hA _), Real.mul_rpow hN.le (pow_nonneg hB _),
      ← Real.rpow_natCast_mul hA, ← Real.rpow_natCast_mul hB, mul_mul_mul_comm, ← Real.rpow_add hN]
    norm_num [hN.ne', mul_pow, ← pow_mul]
  unfold l2Average
  apply (Real.sqrt_le_left (mul_nonneg hA (sq_nonneg _))).mpr
  unfold average
  apply (div_le_iff₀ hN).mpr
  calc
    _ = ∑ x, |f x * g x^2|^2 := by simp only [abs_mul, abs_pow]
    _ ≤ (∑ x, f x^6)^(2/6 : ℝ) * (∑ x, g x^6)^(2/3 : ℝ) := h
    _ ≤ (N*A^6)^(2/6 : ℝ) * (N*B^6)^(2/3 : ℝ) := by
      have hSq (u : Ω → ℝ) (x : Ω) : 0 ≤ u x^6 := by
        rw [show (6 : ℕ) = 2*3 by decide, pow_mul]
        exact pow_nonneg (sq_nonneg _) _
      exact mul_le_mul (Real.rpow_le_rpow (sum_nonneg fun x _ ↦ hSq f x) hF (by norm_num))
        (Real.rpow_le_rpow (sum_nonneg fun x _ ↦ hSq g x) hG (by norm_num))
        (Real.rpow_nonneg (sum_nonneg fun x _ ↦ hSq g x) _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := hAlg.trans (mul_comm _ _)

/-- Bounds a product of three sign differences times a growth factor. -/
theorem average_abs_mul_sq_mul_le_of_six (f g w : Ω → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : average (fun x ↦ f x ^ 6) ≤ A^6) (hg : average (fun x ↦ g x ^ 6) ≤ B^6) :
    average (fun x ↦ |f x| * |g x|^2 * |w x|) ≤ A * B^2 * l2Average w := by
  have h := average_abs_mul_le_l2Average (fun x ↦ |f x| * |g x|^2) w
  have hAbs (x : Ω) : |(|g x|^2)| = |g x|^2 := abs_of_nonneg (sq_nonneg _)
  simp only [abs_mul, abs_abs, hAbs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (l2Average_mul_sq_le_of_six f g hA hB hf hg) (l2Average_nonneg _))

end LovaszTheta.Circulant
