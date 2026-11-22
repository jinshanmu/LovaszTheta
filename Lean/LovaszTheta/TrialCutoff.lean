module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Logarithmic size and degree cutoff

Both cutoffs are the floor of the sixteenth root of the logarithm.
The finite-order exponential envelopes remain subpolynomial in the
modulus, and the two order-200 tails beat the required log power.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LovaszTheta.Circulant

/-- The common tree size and Hermite degree cutoff. -/
noncomputable def trialCutoff (n : ℕ) : ℕ := ⌊(Real.log (n : ℝ))^(1/16 : ℝ)⌋₊

lemma tendsto_log_nat_atTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma trialCutoff_bounds :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ))^(1/16 : ℝ) / 2 ≤ (trialCutoff n : ℝ) ∧
      (trialCutoff n : ℝ)+1 ≤ 2 * (Real.log (n : ℝ))^(1/16 : ℝ) := by
  have h := (tendsto_rpow_atTop (show 0 < (1/16 : ℝ) by norm_num)).comp tendsto_log_nat_atTop
  filter_upwards [h.eventually_ge_atTop 2,tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn hLog
  change 2 ≤ (Real.log (n : ℝ))^(1/16 : ℝ) at hn
  have h₁ := Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hLog) (1/16 : ℝ))
  have h₂ := Nat.lt_floor_add_one ((Real.log (n : ℝ))^(1/16 : ℝ))
  unfold trialCutoff
  exact ⟨by linarith only [h₂,hn],by linarith only [h₁,hn]⟩

lemma tendsto_trialCutoff_atTop : Tendsto trialCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro k
  have h := (tendsto_rpow_atTop (show 0 < (1/16 : ℝ) by norm_num)).comp tendsto_log_nat_atTop
  filter_upwards [trialCutoff_bounds,h.eventually_ge_atTop (2*(k : ℝ))] with n hn hk
  change 2*(k : ℝ) ≤ (Real.log (n : ℝ))^(1/16 : ℝ) at hk
  exact_mod_cast (show (k : ℝ) ≤ trialCutoff n by linarith only [hn.1,hk])

/-- The exponential envelope at the cutoff grows slower than (n^{1/4}). -/
lemma eventually_cutoff_exp_le (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C*((trialCutoff n : ℝ)+1)^4 ≤ Real.log (n : ℝ)/4 := by
  have h := (tendsto_rpow_atTop (show 0 < (3/4 : ℝ) by norm_num)).comp tendsto_log_nat_atTop
  filter_upwards [trialCutoff_bounds,h.eventually_ge_atTop (64*C),tendsto_log_nat_atTop.eventually_ge_atTop 1]
    with n hn he hp
  let x := Real.log (n : ℝ)
  change 64*C ≤ x^(3/4 : ℝ) at he
  have hx : 0 < x := zero_lt_one.trans_le hp
  have hPow : (x^(1/16 : ℝ))^4 = x^(1/4 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    norm_num
  have hs : ((trialCutoff n : ℝ)+1)^4 ≤ 16*x^(1/4 : ℝ) := by
    refine (pow_le_pow_left₀ (by positivity) hn.2 4).trans_eq ?_
    rw [mul_pow,hPow]
    norm_num
  have hExp : x^(1/4 : ℝ)*x^(3/4 : ℝ) = x := by
    rw [← Real.rpow_add hx,show (1/4 : ℝ)+3/4 = 1 by norm_num,Real.rpow_one]
  exact (mul_le_mul_of_nonneg_left hs hC).trans
    (show C*(16*x^(1/4 : ℝ)) ≤ x/4 by
      have h₁ := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hx.le (1/4 : ℝ))
      linarith only [h₁,hExp])

/-- The inverse-square-root finite-order error vanishes after multiplication
by any fixed logarithmic power. -/
theorem tendsto_log_pow_cutoff_exp_div_sqrt (r : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))^r *
      (Real.exp (C*((trialCutoff n : ℝ)+1)^4)/Real.sqrt n)) atTop (𝓝 0) := by
  have hUpper := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r : ℝ) (1/4)
    (by norm_num)).comp tendsto_log_nat_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hn) _) (by positivity)
  · filter_upwards [eventually_cutoff_exp_le C hC,eventually_ge_atTop (1 : ℕ),
      tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn hp hL
    simp only [Function.comp_apply,Real.rpow_natCast]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hL) _)
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hp)
    calc
      _ ≤ Real.exp (Real.log (n : ℝ)/4) / Real.sqrt n :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hn) (by positivity)
      _ = _ := by
        rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hnp,div_eq_mul_inv,← Real.exp_neg,← Real.exp_add]
        congr 1
        ring

/-- The order-200 Gaussian tails vanish even at log power twelve. -/
theorem tendsto_log_pow_div_trialCutoff_pow :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))^12/(trialCutoff n : ℝ)^200) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/2 by norm_num)).comp tendsto_log_nat_atTop
  have h' := h.const_mul ((2 : ℝ)^200)
  simp only [mul_zero] at h'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h'
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hL
    exact div_nonneg (pow_nonneg (zero_le_one.trans hL) _) (by positivity)
  · filter_upwards [trialCutoff_bounds,tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn hL
    let x := Real.log (n : ℝ)
    have hx : 0 < x := zero_lt_one.trans_le hL
    have hP : 0 < (x^(1/16 : ℝ)/2)^200 := by positivity
    have he : (x^(1/16 : ℝ))^200 = x^(25/2 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
      norm_num
    change x^12/(trialCutoff n : ℝ)^200 ≤ (2 : ℝ)^200*x^(-(1/2) : ℝ)
    calc
      _ ≤ x^12/(x^(1/16 : ℝ)/2)^200 :=
        div_le_div_of_nonneg_left (pow_nonneg hx.le _) hP (pow_le_pow_left₀ (by positivity) hn.1 _)
      _ = _ := by
        rw [div_pow,he,div_div_eq_mul_div,mul_comm (x^12),mul_div_assoc,← Real.rpow_natCast x 12,
          ← Real.rpow_sub hx]
        norm_num

end LovaszTheta.Circulant
