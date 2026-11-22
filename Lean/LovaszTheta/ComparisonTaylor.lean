module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic

/-!
# Taylor remainder for the sign flip

The first-order Taylor expansion uses a bound on the second
derivative on the segment between the original and flipped inputs.
-/

@[expose] public section

open Set
open scoped Interval

namespace LovaszTheta.Circulant

/-- The first-order Taylor remainder with polynomial derivative growth. -/
theorem abs_taylor_remainder_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (r : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ z, |iteratedDeriv 2 f z| ≤ C*(1+|z|)^r) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤
      (C/2) * |y-x|^2 * (1+max |x| |y|)^r := by
  by_cases he : x = y
  · subst y
    simp
  obtain ⟨z, hz, hEq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) he hf.contDiffOn
  have hDer := ((hf.differentiable (by norm_num)) x).hasDerivAt
  have hUniq := uniqueDiffOn_uIcc he x left_mem_uIcc
  have hD : derivWithin f [[x,y]] x = deriv f x := hDer.hasDerivWithinAt.derivWithin hUniq
  have hPoly : taylorWithinEval f 1 [[x,y]] x y = f x + deriv f x * (y-x) := by
    have h := taylorWithinEval_succ f 0 [[x,y]] x y
    simpa only [zero_add, taylor_within_zero_eval, Nat.cast_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, inv_one, pow_one, one_mul, iteratedDerivWithin_one, hD, smul_eq_mul, mul_comm] using h
  rw [hPoly] at hEq
  have hAbs : |z| ≤ max |x| |y| := by
    have hp := mem_uIcc.mp (uIoo_subset_uIcc_self hz)
    apply abs_le.mpr
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := hp
    · constructor
      · exact (neg_le_neg (le_max_left |x| |y|)).trans ((neg_abs_le x).trans h₁)
      · exact h₂.trans ((le_abs_self y).trans (le_max_right _ _))
    · constructor
      · exact (neg_le_neg (le_max_right |x| |y|)).trans ((neg_abs_le y).trans h₁)
      · exact h₂.trans ((le_abs_self x).trans (le_max_left _ _))
  have hBase : 1+|z| ≤ 1+max |x| |y| := by linarith only [hAbs]
  have hGrow := (hg z).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hBase r) hC)
  rw [sub_sub, hEq]
  norm_num only [Nat.reduceAdd, Nat.factorial_succ, Nat.factorial_zero, Nat.reduceMul, Nat.cast_ofNat]
  rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (C*(1+max |x| |y|)^r) * |y-x|^2 / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hGrow (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

end LovaszTheta.Circulant
