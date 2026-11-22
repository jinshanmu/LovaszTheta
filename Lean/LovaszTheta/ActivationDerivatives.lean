module

public import LovaszTheta.Activation
public import LovaszTheta.HermiteMoments
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Higher derivatives of the activation

Each derivative has a polynomial numerator of degree at most its
order. The positive quadratic in the denominator bounds it uniformly
on bounded intervals and supplies decay outside them.
-/

@[expose] public section

open Finset Polynomial
open scoped Polynomial

namespace LovaszTheta.Circulant

private noncomputable def activationNumerator (τ : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | j+1 => (X^2+C (4*τ))*(activationNumerator τ j).derivative +
      C (1-2*(j : ℝ))*X*activationNumerator τ j

private lemma natDegree_activationNumerator_le (τ : ℝ) (j : ℕ) :
    (activationNumerator τ j).natDegree ≤ j := by
  induction j with
  | zero => simp [activationNumerator]
  | succ j ih =>
    by_cases hj : j = 0
    · subst j
      simp [activationNumerator]
    · rw [activationNumerator]
      have hQ : (X^2+C (4*τ) : ℝ[X]).natDegree ≤ 2 := by
        exact (natDegree_add_le _ _).trans
          (by simp only [natDegree_X_pow, natDegree_C, max_eq_left (Nat.zero_le _), le_refl])
      have hC : (C (1-2*(j : ℝ))*X : ℝ[X]).natDegree ≤ 1 := by
        exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl])
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have hd := (natDegree_derivative_le (activationNumerator τ j)).trans
          (Nat.sub_le_sub_right ih 1)
        exact natDegree_mul_le.trans (by omega)
      · exact natDegree_mul_le.trans (by omega)

private lemma iteratedDeriv_activation_formula {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    iteratedDeriv j (activation τ) =
      fun x ↦ (activationNumerator τ j).eval x * (x^2+4*τ)^(1/2-(j : ℝ)) := by
  induction j with
  | zero =>
    funext x
    simp [activationNumerator, activation, Real.sqrt_eq_rpow]
  | succ j ih =>
    funext x
    let a := (1/2 : ℝ)-(j : ℝ)
    let q (y : ℝ) := y^2+4*τ
    let P := activationNumerator τ j
    have hq : 0 < q x := by unfold q; positivity
    have hqD : HasDerivAt q (2*x) x := by
      convert (hasDerivAt_pow 2 x).add_const (4*τ) using 1
      norm_num
    have hPow := hqD.rpow_const (p := a) (Or.inl hq.ne')
    have hD : HasDerivAt (fun y ↦ P.eval y*(q y)^a)
        (P.derivative.eval x*(q x)^a + P.eval x*(2*x*a*(q x)^(a-1))) x :=
      (P.hasDerivAt x).mul hPow
    have hFactor : q x*(q x)^(a-1) = (q x)^a := by
      calc
        _ = (q x)^(1 : ℝ)*(q x)^(a-1) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hq]; congr 1; ring
    rw [iteratedDeriv_succ, ih]
    change deriv (fun y ↦ P.eval y*(q y)^a) x = _
    rw [hD.deriv]
    calc
      _ = (q x*P.derivative.eval x+(1-2*(j : ℝ))*x*P.eval x)*(q x)^(a-1) := by
        rw [← hFactor]
        unfold a
        ring
      _ = _ := by
        change _ = (activationNumerator τ (j+1)).eval x*(q x)^((1/2 : ℝ)-((j+1 : ℕ) : ℝ))
        rw [activationNumerator, eval_add, eval_mul, eval_mul, eval_mul, eval_add, eval_pow, eval_C, eval_C, eval_X]
        have he : (1/2 : ℝ)-((j+1 : ℕ) : ℝ) = a-1 := by push_cast; unfold a; ring
        rw [he]

/-- Every positive-order derivative of the smoothed absolute value is bounded. -/
theorem exists_bound_abs_iteratedDeriv_activation {τ : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j (activation τ) x| ≤ C := by
  let P := activationNumerator τ j
  let a := (1/2 : ℝ)-(j : ℝ)
  let A := ∑ k ∈ P.support, |P.coeff k|
  let K := A*(2 : ℝ)^j
  have hA : 0 ≤ A := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hK : 0 ≤ K := by unfold K; positivity
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ha : a ≤ 0 := by unfold a; linarith
  refine ⟨K*max 1 ((4*τ)^a), mul_nonneg hK ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left _ _)), ?_⟩
  intro x
  let y := |x|
  let q := x^2+4*τ
  have hq : 0 < q := by unfold q; positivity
  rw [iteratedDeriv_activation_formula hτ j]
  change |P.eval x*q^a| ≤ _
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  have hEval : |P.eval x| ≤ A*(1+y)^j := by
    refine (abs_eval_le_coeff_sum P x).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x])
      (natDegree_activationNumerator_le τ j)) hA
  by_cases hSmall : y ≤ 1
  · have hP : |P.eval x| ≤ K :=
      hEval.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) hA)
    have hR : q^a ≤ (4*τ)^a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold q; linarith [sq_nonneg x]) ha
    exact mul_le_mul hP (hR.trans (le_max_right _ _)) (Real.rpow_nonneg hq.le _) hK
  · have hy : 1 ≤ y := le_of_not_ge hSmall
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hP : |P.eval x| ≤ K*y^j := by
      calc
        _ ≤ A*(2*y)^j := hEval.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) _) hA)
        _ = _ := by unfold K; rw [mul_pow, mul_assoc]
    have hR : q^a ≤ (y^2)^a := by
      apply Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hy0) _ ha
      unfold y q
      rw [sq_abs]
      linarith
    have hExp : y^j*(y^2)^a = y^(1-(j : ℝ)) := by
      rw [← Real.rpow_natCast_mul hy0.le, ← Real.rpow_natCast y j, ← Real.rpow_add hy0]
      congr 1
      unfold a
      push_cast
      ring
    have hBound : y^(1-(j : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
    calc
      _ ≤ (K*y^j)*(y^2)^a := mul_le_mul hP hR (Real.rpow_nonneg hq.le _) (by positivity)
      _ = K*y^(1-(j : ℝ)) := by rw [mul_assoc, hExp]
      _ ≤ K*1 := mul_le_mul_of_nonneg_left hBound hK
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hK

/-- Bounds the positive-order derivatives after rescaling the input by
any nonnegative Gaussian scale within the manuscript's variance range. -/
theorem exists_bound_abs_iteratedDeriv_scaled_activation {τ : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, 0 ≤ σ → σ ≤ Real.sqrt (2*Real.pi) →
      ∀ x, |iteratedDeriv j (fun g ↦ activation τ (σ*g)) x| ≤ C := by
  obtain ⟨C, hC, hDer⟩ := exists_bound_abs_iteratedDeriv_activation hτ hj
  refine ⟨(Real.sqrt (2*Real.pi))^j*C, by positivity, ?_⟩
  intro σ hσ hσ' x
  rw [iteratedDeriv_comp_const_mul (contDiff_activation hτ), abs_mul, abs_of_nonneg (pow_nonneg hσ _)]
  exact mul_le_mul (pow_le_pow_left₀ hσ hσ' _) (hDer (σ*x)) (abs_nonneg _) (by positivity)

end LovaszTheta.Circulant
