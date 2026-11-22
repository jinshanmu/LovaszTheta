module

public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

/-!
# Chebyshev polynomials for the semicircle law

Use the cosine coordinate for the semicircle integral. The sine
formula gives orthonormality. The Chebyshev differential equation
and integration by parts give the derivative energy.
-/

@[expose] public section

open Finset Polynomial Real Set
open scoped Polynomial

namespace LovaszTheta.Independent

/-- The second-kind Chebyshev polynomial with argument scaled by one half. -/
noncomputable def semicircleChebyshev (j : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.U ℝ j).comp (C (1/2)*X)

@[simp]
lemma semicircleChebyshev_zero : semicircleChebyshev 0 = 1 := by simp [semicircleChebyshev]

@[simp]
lemma semicircleChebyshev_one : semicircleChebyshev 1 = X := by
  simp only [semicircleChebyshev,Nat.cast_one,Polynomial.Chebyshev.U_one,mul_comp,ofNat_comp,X_comp]
  rw [← mul_assoc,← C_eq_natCast,← map_mul]
  norm_num

lemma semicircleChebyshev_add_two (j : ℕ) :
    semicircleChebyshev (j+2) = X*semicircleChebyshev (j+1)-semicircleChebyshev j := by
  simp only [semicircleChebyshev,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Polynomial.Chebyshev.U_add_two,
    sub_comp,mul_comp,X_comp,ofNat_comp]
  have h : (2 : ℝ[X])*(C (1/2)*X) = X := by
    rw [← mul_assoc,← C_ofNat,← map_mul]
    norm_num
  rw [h]

lemma eval_semicircleChebyshev (j : ℕ) (x : ℝ) :
    (semicircleChebyshev j).eval x = (Polynomial.Chebyshev.U ℝ j).eval (x/2) := by
  rw [semicircleChebyshev,eval_comp,eval_mul,eval_C,eval_X]
  ring_nf

private lemma natDegree_halfX : (C (1/2)*X : ℝ[X]).natDegree = 1 := by
  rw [natDegree_C_mul (by norm_num),natDegree_X]

lemma monic_semicircleChebyshev (j : ℕ) : (semicircleChebyshev j).Monic := by
  rw [Monic,semicircleChebyshev,leadingCoeff_comp (by rw [natDegree_halfX]; decide),
    Polynomial.Chebyshev.leadingCoeff_U_natCast,Polynomial.Chebyshev.natDegree_U_natCast,
    leadingCoeff_mul,leadingCoeff_C,leadingCoeff_X,mul_one,← mul_pow]
  norm_num

lemma natDegree_semicircleChebyshev (j : ℕ) : (semicircleChebyshev j).natDegree = j := by
  rw [semicircleChebyshev,natDegree_comp,natDegree_halfX,Polynomial.Chebyshev.natDegree_U_natCast,mul_one]

/-- The semicircle integral in the variable x = 2 cos t. -/
noncomputable def semicircleAverage (f : ℝ → ℝ) : ℝ :=
  (2/π)*∫ t in 0..π, f (2*cos t)*(sin t)^2

private lemma integral_cos_int_mul (k : ℤ) :
    (∫ t in (0 : ℝ)..π, cos ((k : ℝ)*t)) = if k = 0 then π else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hDeriv (t : ℝ) :
      HasDerivAt (fun x ↦ sin ((k : ℝ)*x)/(k : ℝ)) (cos ((k : ℝ)*t)) t := by
    have h := ((hasDerivAt_sin ((k : ℝ)*t)).comp t ((hasDerivAt_id t).const_mul (k : ℝ))).div_const (k : ℝ)
    change HasDerivAt (fun x ↦ sin ((k : ℝ)*x)/(k : ℝ))
      (cos ((k : ℝ)*t)*((k : ℝ)*1)/(k : ℝ)) t at h
    simpa only [mul_one,mul_div_cancel_right₀ _ hk'] using h
  have hInt : IntervalIntegrable (fun t : ℝ ↦ cos ((k : ℝ)*t)) MeasureTheory.volume 0 π :=
    (continuous_cos.comp (continuous_id.const_mul _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hDeriv t) hInt]
  simp [hk,Real.sin_int_mul_pi]

private lemma integral_sin_family_mul (i j : ℕ) :
    (∫ t in (0 : ℝ)..π, sin (((i : ℝ)+1)*t)*sin (((j : ℝ)+1)*t)) =
      if i = j then π/2 else 0 := by
  let a : ℤ := (i : ℤ)-(j : ℤ)
  let b : ℤ := (i : ℤ)+(j : ℤ)+2
  have he (t : ℝ) : sin (((i : ℝ)+1)*t)*sin (((j : ℝ)+1)*t) =
      (cos ((a : ℝ)*t)-cos ((b : ℝ)*t))/2 := by
    rw [show (a : ℝ)*t = ((i : ℝ)+1)*t-((j : ℝ)+1)*t by unfold a; push_cast; ring,
      show (b : ℝ)*t = ((i : ℝ)+1)*t+((j : ℝ)+1)*t by unfold b; push_cast; ring,cos_sub,cos_add]
    ring
  have hInt (c : ℤ) : IntervalIntegrable (fun t : ℝ ↦ cos ((c : ℝ)*t)) MeasureTheory.volume 0 π :=
    (continuous_cos.comp (continuous_id.const_mul _)).intervalIntegrable _ _
  simp_rw [he,intervalIntegral.integral_div,intervalIntegral.integral_sub (hInt a) (hInt b),
    integral_cos_int_mul]
  have hB : b ≠ 0 := by unfold b; omega
  have hA : a = 0 ↔ i = j := by unfold a; omega
  simp only [hB,ite_false,sub_zero,hA]
  split_ifs
  · rfl
  · norm_num

lemma semicircleChebyshev_sine (j : ℕ) (t : ℝ) :
    (semicircleChebyshev j).eval (2*cos t)*sin t = sin (((j : ℝ)+1)*t) := by
  rw [eval_semicircleChebyshev,show 2*cos t/2 = cos t by ring]
  simpa only [Int.cast_natCast] using Polynomial.Chebyshev.U_real_cos t (j : ℤ)

/-- The Chebyshev polynomials are orthonormal for the semicircle law. -/
theorem semicircleAverage_chebyshev_mul (i j : ℕ) :
    semicircleAverage (fun x ↦ (semicircleChebyshev i).eval x*(semicircleChebyshev j).eval x) =
      if i = j then 1 else 0 := by
  have he (t : ℝ) :
      ((semicircleChebyshev i).eval (2*cos t)*(semicircleChebyshev j).eval (2*cos t))*(sin t)^2 =
        sin (((i : ℝ)+1)*t)*sin (((j : ℝ)+1)*t) := by
    rw [← semicircleChebyshev_sine i,← semicircleChebyshev_sine j]
    ring
  simp_rw [semicircleAverage,he,integral_sin_family_mul]
  split_ifs
  · field_simp [Real.pi_ne_zero]
  · norm_num

@[simp]
lemma semicircleAverage_one : semicircleAverage (fun _ ↦ 1) = 1 := by
  simpa only [semicircleChebyshev_zero,eval_one,one_mul,ite_true] using semicircleAverage_chebyshev_mul 0 0

@[simp]
lemma semicircleAverage_sq : semicircleAverage (fun x ↦ x^2) = 1 := by
  simpa only [semicircleChebyshev_one,eval_X,← pow_two,ite_true] using semicircleAverage_chebyshev_mul 1 1

lemma semicircleAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ Set.Icc (-2 : ℝ) 2, f x ≤ g x) : semicircleAverage f ≤ semicircleAverage g := by
  unfold semicircleAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on Real.pi_pos.le
    (((hf.comp (continuous_cos.const_mul _)).mul (continuous_sin.pow _)).intervalIntegrable _ _)
    (((hg.comp (continuous_cos.const_mul _)).mul (continuous_sin.pow _)).intervalIntegrable _ _)
  intro t _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact h _ ⟨by linarith [neg_one_le_cos t],by linarith [cos_le_one t]⟩

private lemma derivative_semicircleChebyshev (j : ℕ) :
    derivative (semicircleChebyshev j) =
      C (1/2)*((Polynomial.Chebyshev.U ℝ j).derivative.comp (C (1/2)*X)) := by
  rw [semicircleChebyshev,derivative_comp]
  simp only [derivative_mul,derivative_C,derivative_X,zero_mul,mul_one,zero_add]

private lemma derivative_derivative_semicircleChebyshev (j : ℕ) :
    derivative (derivative (semicircleChebyshev j)) =
      C (1/4)*((derivative (derivative (Polynomial.Chebyshev.U ℝ j))).comp (C (1/2)*X)) := by
  rw [derivative_semicircleChebyshev,derivative_mul,derivative_C,zero_mul,zero_add,derivative_comp,
    derivative_mul,derivative_C,zero_mul,zero_add,derivative_X,mul_one,← mul_assoc,← map_mul]
  norm_num

/-- The differential equation after the change of variable from x/2 to x. -/
theorem semicircleChebyshev_differential (j : ℕ) (x : ℝ) :
    (4-x^2)*(derivative (derivative (semicircleChebyshev j))).eval x -
      3*x*(derivative (semicircleChebyshev j)).eval x + (j : ℝ)*(j+2)*(semicircleChebyshev j).eval x = 0 := by
  have h := congrArg (fun p : ℝ[X] ↦ p.eval (x/2))
    (Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := ℝ) (j : ℤ))
  simp only [eval_mul,eval_sub,eval_pow,eval_X,eval_one,eval_add,eval_ofNat,Int.cast_natCast,eval_natCast,
    Function.iterate_succ,Function.iterate_zero_apply,Function.comp_apply] at h
  rw [derivative_derivative_semicircleChebyshev,derivative_semicircleChebyshev,eval_semicircleChebyshev]
  simp only [eval_mul,eval_comp,eval_C,eval_X]
  rw [show 1/2*x = x/2 by ring]
  linear_combination (norm := ring_nf) h

/-- Integration by parts against the semicircle weight gives the diagonal derivative form. -/
theorem semicircleAverage_derivative_mul_chebyshev (p : ℝ[X]) (j : ℕ) :
    semicircleAverage (fun x ↦ (4-x^2)*p.derivative.eval x*(semicircleChebyshev j).derivative.eval x) =
      (j : ℝ)*(j+2)*semicircleAverage (fun x ↦ p.eval x*(semicircleChebyshev j).eval x) := by
  let q := semicircleChebyshev j
  let x (t : ℝ) := 2*cos t
  let F (t : ℝ) := p.eval (x t)*q.derivative.eval (x t)*(sin t)^3
  let G (t : ℝ) := (4-(x t)^2)*p.derivative.eval (x t)*q.derivative.eval (x t)*(sin t)^2
  let E (t : ℝ) := p.eval (x t)*q.eval (x t)*(sin t)^2
  let a : ℝ := (j : ℝ)*(j+2)
  have hDeriv (t : ℝ) : HasDerivAt F ((a*E t-G t)/2) t := by
    have hx : HasDerivAt x (-2*sin t) t := by
      have h := (hasDerivAt_cos t).const_mul 2
      convert h using 1
      ring
    have hp := (p.hasDerivAt (x t)).comp t hx
    have hq := (q.derivative.hasDerivAt (x t)).comp t hx
    refine ((hp.mul hq).mul ((hasDerivAt_sin t).pow 3)).congr_deriv ?_
    have hSin : 4-(x t)^2 = 4*(sin t)^2 := by unfold x; nlinarith only [sin_sq_add_cos_sq t]
    have hDiff := semicircleChebyshev_differential j (x t)
    change (4-(x t)^2)*q.derivative.derivative.eval (x t) -
      3*(x t)*q.derivative.eval (x t) + a*q.eval (x t) = 0 at hDiff
    unfold E G
    rw [hSin] at hDiff ⊢
    change _ = (a*(p.eval (x t)*q.eval (x t)*(sin t)^2) -
      4*(sin t)^2*p.derivative.eval (x t)*q.derivative.eval (x t)*(sin t)^2)/2
    simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
    linear_combination (norm := (unfold x; ring_nf)) -p.eval (x t)*(sin t)^2/2*hDiff
  have hxC : Continuous x := continuous_cos.const_mul _
  have hE : IntervalIntegrable E MeasureTheory.volume 0 π :=
    ((((p.continuous.comp hxC).mul (q.continuous.comp hxC)).mul (continuous_sin.pow _))).intervalIntegrable _ _
  have hG : IntervalIntegrable G MeasureTheory.volume 0 π :=
    (((((continuous_const.sub (hxC.pow 2)).mul (p.derivative.continuous.comp hxC)).mul
      (q.derivative.continuous.comp hxC)).mul (continuous_sin.pow _))).intervalIntegrable _ _
  have hI : IntervalIntegrable (fun t ↦ (a*E t-G t)/2) MeasureTheory.volume 0 π :=
    ((hE.const_mul a).sub hG).div_const 2
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hDeriv t) hI
  have hE' : IntervalIntegrable (fun t ↦ a*E t) MeasureTheory.volume 0 π := hE.const_mul a
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub hE' hG,intervalIntegral.integral_const_mul] at hb
  simp only [F,sin_pi,sin_zero,zero_pow (by decide : (3 : ℕ) ≠ 0),mul_zero,sub_zero] at hb
  change (2/π)*(∫ t in 0..π, G t) = a*((2/π)*(∫ t in 0..π, E t))
  have he : (∫ t in 0..π, G t) = a*(∫ t in 0..π, E t) := by linarith only [hb]
  rw [he]
  ring

end LovaszTheta.Independent
