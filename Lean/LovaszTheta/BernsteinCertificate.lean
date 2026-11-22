module

public import LovaszTheta.PolynomialCertificate

/-!
# The Bernstein certificate polynomial

The absolute-value data are symmetric. Differentiating the
Bernstein basis gives the average of adjacent differences used in
the derivative energy estimate.
-/

@[expose] public section

open Finset Polynomial
open scoped Polynomial unitInterval

namespace LovaszTheta.Independent

/-- Sample of the absolute-value function at a Bernstein grid point. -/
noncomputable def absoluteValueSample (N j : ℕ) : ℝ := |4*(j : ℝ)/N-2|

/-- The Bernstein polynomial in the unit-interval coordinate. -/
noncomputable def bernsteinAbsUnitPolynomial (N : ℕ) : ℝ[X] :=
  ∑ j ∈ range (N+1), C (absoluteValueSample N j)*bernsteinPolynomial ℝ N j

/-- The manuscript's polynomial on the interval `[-2,2]`. -/
noncomputable def bernsteinAbsPolynomial (N : ℕ) : ℝ[X] :=
  (bernsteinAbsUnitPolynomial N).comp (C (1/4)*(X+2))

lemma eval_bernsteinAbsPolynomial (N : ℕ) (x : ℝ) :
    (bernsteinAbsPolynomial N).eval x = (bernsteinAbsUnitPolynomial N).eval ((x+2)/4) := by
  simp only [bernsteinAbsPolynomial,eval_comp,eval_mul,eval_C,eval_add,eval_X,eval_ofNat]
  ring_nf

lemma eval_bernsteinAbsUnitPolynomial (N : ℕ) (t : I) :
    (bernsteinAbsUnitPolynomial N).eval (t : ℝ) = bernsteinAbs N t := by
  unfold bernsteinAbsUnitPolynomial bernsteinAbs absoluteValueSample
  simp only [eval_finsetSum,eval_mul,eval_C,bernstein.z,Finset.sum_range]
  apply sum_congr rfl
  intro j _
  have h (i : ℕ) : (bernsteinPolynomial ℝ N i).eval (t : ℝ) = bernstein N i t := rfl
  rw [h]
  ring_nf

/-- The polynomial extends the Jensen and variance bounds on the full interval. -/
theorem bernsteinAbsPolynomial_bounds {N : ℕ} (hN : N ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (-2) 2) :
    |x| ≤ (bernsteinAbsPolynomial N).eval x ∧
      (bernsteinAbsPolynomial N).eval x-|x| ≤ 2/Real.sqrt N := by
  let t : I := ⟨(x+2)/4,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have he : 4*(t : ℝ)-2 = x := by change 4*((x+2)/4)-2 = x; ring
  rw [eval_bernsteinAbsPolynomial,show (x+2)/4 = (t : ℝ) from rfl,eval_bernsteinAbsUnitPolynomial]
  exact ⟨he ▸ abs_le_bernsteinAbs hN t,he ▸ bernsteinAbs_sub_abs_le hN t⟩

private lemma absoluteValueSample_reflect {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    absoluteValueSample N (N-j) = absoluteValueSample N j := by
  unfold absoluteValueSample
  rw [Nat.cast_sub hj]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show 4*((N : ℝ)-j)/N-2 = -(4*(j : ℝ)/N-2) by field_simp [hN']; ring,abs_neg]

/-- Reflection of the Bernstein grid makes the polynomial even. -/
theorem bernsteinAbsPolynomial_even {N : ℕ} (hN : 0 < N) :
    (bernsteinAbsPolynomial N).eval.Even := by
  intro x
  simp only [eval_bernsteinAbsPolynomial,bernsteinAbsUnitPolynomial,eval_finsetSum,eval_mul,eval_C]
  have h : (-x+2)/4 = 1-(x+2)/4 := by ring
  rw [h]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ N := Nat.le_of_lt_succ (mem_range.mp hj)
  have he := congrArg (fun p : ℝ[X] ↦ p.eval ((x+2)/4)) (bernsteinPolynomial.flip ℝ N j hj')
  simp only [eval_comp,eval_sub,eval_one,eval_X] at he
  simp only [Nat.add_sub_cancel]
  rw [he,absoluteValueSample_reflect hN hj']

private lemma derivative_bernstein_data (N : ℕ) (d : ℕ → ℝ) :
    derivative (∑ j ∈ range (N+2), C (d j)*bernsteinPolynomial ℝ (N+1) j) =
      (N+1 : ℝ[X])*∑ j ∈ range (N+1), C (d (j+1)-d j)*bernsteinPolynomial ℝ N j := by
  let B := bernsteinPolynomial ℝ N
  let f (j : ℕ) := C (d j)*B j
  have hShift : (∑ j ∈ range (N+1), f (j+1))+f 0 = ∑ j ∈ range (N+1), f j := by
    rw [← sum_range_succ',sum_range_succ]
    have ht : B (N+1) = 0 := bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self N)
    simp only [f,ht,mul_zero,add_zero]
  rw [sum_range_succ',map_add,map_sum]
  simp only [derivative_mul,derivative_C,zero_mul,zero_add,bernsteinPolynomial.derivative_succ,
    bernsteinPolynomial.derivative_zero,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  have hL (j : ℕ) : C (d (j+1))*((N+1 : ℝ[X])*(B j-B (j+1))) =
      (N+1 : ℝ[X])*(C (d (j+1))*B j-f (j+1)) := by unfold f; ring
  change (∑ j ∈ range (N+1), C (d (j+1))*((N+1 : ℝ[X])*(B j-B (j+1))))+
    C (d 0)*(-(N+1 : ℝ[X])*B 0) = _
  simp_rw [hL,← mul_sum,sum_sub_distrib]
  have hh : (∑ j ∈ range (N+1), C (d (j+1)-d j)*B j) =
      (∑ j ∈ range (N+1), C (d (j+1))*B j) - ∑ j ∈ range (N+1), f j := by
    simp_rw [map_sub,sub_mul,sum_sub_distrib,f]
  change _ = (N+1 : ℝ[X]) * ∑ j ∈ range (N+1), C (d (j+1)-d j)*B j
  rw [hh,← hShift]
  unfold f
  ring

private lemma abs_absoluteValueSample_succ_sub {N : ℕ} (hN : 0 < N) (j : ℕ) :
    |absoluteValueSample N (j+1)-absoluteValueSample N j| ≤ 4/(N : ℝ) := by
  unfold absoluteValueSample
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans_eq ?_
  rw [Nat.cast_add,Nat.cast_one,show 4*((j : ℝ)+1)/N-2-(4*(j : ℝ)/N-2) = 4/N by ring]
  exact abs_of_nonneg (by positivity)

/-- The Bernstein derivative has magnitude at most one on `[-2,2]`. -/
theorem abs_derivative_bernsteinAbsPolynomial_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Icc (-2) 2) : |(derivative (bernsteinAbsPolynomial N)).eval x| ≤ 1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let t : I := ⟨(x+2)/4,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  let d := absoluteValueSample (n+1)
  have hn : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hEval (j : ℕ) : (bernsteinPolynomial ℝ n j).eval ((x+2)/4) = bernstein n j t := rfl
  have hProb : (∑ j ∈ range (n+1), bernstein n j t) = 1 := by
    rw [sum_range]
    exact bernstein.probability n t
  have h : (derivative (bernsteinAbsPolynomial (n+1))).eval x =
      ((n : ℝ)+1)/4 * (∑ j ∈ range (n+1), (d (j+1)-d j)*bernstein n j t) := by
    unfold bernsteinAbsPolynomial
    rw [derivative_comp]
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,derivative_add,derivative_X,
      derivative_ofNat,mul_one,add_zero,eval_mul,eval_C,eval_comp,eval_add,eval_X,eval_ofNat]
    unfold bernsteinAbsUnitPolynomial
    rw [derivative_bernstein_data n d]
    simp only [eval_mul,eval_add,eval_natCast,eval_one,eval_finsetSum,eval_C]
    rw [show 1/4*(x+2) = (x+2)/4 by ring]
    simp_rw [hEval]
    ring
  rw [h,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ)+1)/4)]
  have hh : |∑ j ∈ range (n+1), (d (j+1)-d j)*bernstein n j t| ≤ 4/((n : ℝ)+1) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul,abs_of_nonneg (bernstein_nonneg (x := t))]
    calc
      _ ≤ ∑ j ∈ range (n+1), (4/((n : ℝ)+1))*bernstein n j t := sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_right
          (by simpa only [d,Nat.cast_succ] using abs_absoluteValueSample_succ_sub hN j)
          bernstein_nonneg
      _ = _ := by rw [← mul_sum,hProb,mul_one]
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq ?_
  field_simp [hn.ne']

end LovaszTheta.Independent
