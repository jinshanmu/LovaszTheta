module

public import LovaszTheta.BernsteinCertificate
public import LovaszTheta.SemicircleExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The nonnegative certificate polynomial

The Bernstein approximation is even, and its derivative energy
bounds the Chebyshev coefficients. Its constant coefficient and
the normalized single-edge coefficient have the same limit.
-/

@[expose] public section

open Finset Polynomial Filter
open scoped Polynomial Topology

namespace LovaszTheta.Independent

lemma natDegree_bernsteinAbsPolynomial_le (N : ℕ) :
    (bernsteinAbsPolynomial N).natDegree ≤ N := by
  have hLine : (C (1/4)*(X+2) : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans ?_)
    simp
  have hBase (j : ℕ) (hj : j ≤ N) : (bernsteinPolynomial ℝ N j).natDegree ≤ N := by
    rw [bernsteinPolynomial,mul_assoc,← C_eq_natCast]
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have h : ((1-X : ℝ[X]).natDegree) ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    have h' : ((1-X : ℝ[X])^(N-j)).natDegree ≤ N-j :=
      natDegree_pow_le.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (N-j) h)
    exact (add_le_add (by simp : ((X : ℝ[X])^j).natDegree ≤ j) h').trans_eq (Nat.add_sub_of_le hj)
  have hU : (bernsteinAbsUnitPolynomial N).natDegree ≤ N := by
    unfold bernsteinAbsUnitPolynomial
    exact natDegree_sum_le_of_forall_le _ _ fun j hj ↦
      (natDegree_C_mul_le _ _).trans (hBase j (Nat.le_of_lt_succ (mem_range.mp hj)))
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hU hLine).trans_eq (Nat.mul_one _))

/-- Degrees of the nonlinear terms in the Chebyshev expansion. -/
def nonlinearDegrees (N : ℕ) : Finset ℕ := (range (N+1)).filter (fun j ↦ 2 ≤ j)

lemma mem_nonlinearDegrees {N j : ℕ} :
    j ∈ nonlinearDegrees N ↔ 2 ≤ j ∧ j ≤ N := by
  unfold nonlinearDegrees
  rw [mem_filter,mem_range]
  omega

private lemma sum_chebyshevDegrees {R : Type*} [AddCommMonoid R] {N : ℕ} (hN : 0 < N) (f : ℕ → R) :
    (∑ j ∈ range (N+1), f j) = f 0+f 1+∑ j ∈ nonlinearDegrees N, f j := by
  have he : range (N+1) = insert 0 (insert 1 (nonlinearDegrees N)) := by
    ext j
    simp only [mem_range,mem_insert,mem_nonlinearDegrees]
    omega
  have h0 : 0 ∉ insert 1 (nonlinearDegrees N) := by simp [mem_nonlinearDegrees]
  have h1 : 1 ∉ nonlinearDegrees N := by simp [mem_nonlinearDegrees]
  rw [he,sum_insert h0,sum_insert h1,add_assoc]

/-- The Bernstein approximation's Chebyshev coefficients. -/
noncomputable def bernsteinCoefficient (N j : ℕ) : ℝ :=
  semicircleCoefficient (bernsteinAbsPolynomial N) j

/-- The nonnegative polynomial used in the spectral certificate. -/
noncomputable def certificatePolynomial (N : ℕ) : ℝ[X] := X+bernsteinAbsPolynomial N

theorem certificatePolynomial_nonneg {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Icc (-2) 2) : 0 ≤ (certificatePolynomial N).eval x := by
  have h := (bernsteinAbsPolynomial_bounds hN.ne' hx).1
  simp only [certificatePolynomial,eval_add,eval_X]
  linarith only [h,neg_le_abs x]

lemma bernsteinCoefficient_one {N : ℕ} (hN : 0 < N) : bernsteinCoefficient N 1 = 0 :=
  semicircleCoefficient_one_of_even _ (bernsteinAbsPolynomial_even hN)

/-- The certificate polynomial has the manuscript's Chebyshev expansion. -/
theorem certificatePolynomial_expansion {N : ℕ} (hN : 0 < N) :
    certificatePolynomial N = C (bernsteinCoefficient N 0) + semicircleChebyshev 1 +
      ∑ j ∈ nonlinearDegrees N, C (bernsteinCoefficient N j)*semicircleChebyshev j := by
  have h := chebyshev_expansion (bernsteinAbsPolynomial N) N (natDegree_bernsteinAbsPolynomial_le N)
  change bernsteinAbsPolynomial N = ∑ j ∈ range (N+1), C (bernsteinCoefficient N j)*semicircleChebyshev j at h
  unfold certificatePolynomial
  rw [h,sum_chebyshevDegrees hN,bernsteinCoefficient_one hN,map_zero,zero_mul,add_zero,
    semicircleChebyshev_zero,mul_one,semicircleChebyshev_one]
  abel

private lemma semicircleAverage_four_sub_sq :
    semicircleAverage (fun x ↦ 4-x^2) = 3 := by
  have h := semicircleAverage_add (f := fun _ ↦ 4) (g := fun x ↦ -(x^2))
    continuous_const (by fun_prop)
  have he := semicircleAverage_const_mul (-1) (· ^ 2)
  simp only [neg_one_mul,semicircleAverage_sq,mul_one] at he
  simp only [semicircleAverage_const,he] at h
  have h' : semicircleAverage (fun x ↦ 4-x^2) = 4 + -1 := h
  linarith only [h']

/-- Squared Chebyshev coefficients weighted by degree have sum at most 3/4. -/
theorem bernsteinCoefficient_energy {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ nonlinearDegrees N, (j : ℝ) * bernsteinCoefficient N j ^ 2 ≤ 3/4 := by
  let p := bernsteinAbsPolynomial N
  let b := bernsteinCoefficient N
  have he := semicircleAverage_derivative_energy p N (natDegree_bernsteinAbsPolynomial_le N)
  change semicircleAverage (fun x ↦ (4-x^2)*(p.derivative.eval x)^2) =
    ∑ j ∈ range (N+1), (j : ℝ)*(j+2)*b j^2 at he
  rw [sum_chebyshevDegrees hN] at he
  have hB : b 1 = 0 := bernsteinCoefficient_one hN
  simp only [Nat.cast_zero,zero_mul,zero_add,hB,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero] at he
  have hI : semicircleAverage (fun x ↦ (4-x^2)*(p.derivative.eval x)^2) ≤ 3 := by
    rw [← semicircleAverage_four_sub_sq]
    apply semicircleAverage_mono
      ((by fun_prop : Continuous (fun x : ℝ ↦ 4-x^2)).mul (p.derivative.continuous.pow 2))
      (by fun_prop)
    intro x hx
    have hW : 0 ≤ 4-x^2 := by
      have hp : |x| ≤ 2 := abs_le.mpr hx
      have hS := pow_le_pow_left₀ (abs_nonneg x) hp 2
      rw [sq_abs] at hS
      nlinarith only [hS]
    have hA := pow_le_pow_left₀ (abs_nonneg _) (abs_derivative_bernsteinAbsPolynomial_le hN hx) 2
    rw [sq_abs,one_pow] at hA
    exact mul_le_of_le_one_right hW hA
  have hSum : (∑ j ∈ nonlinearDegrees N, 4*((j : ℝ)*b j^2)) ≤
      ∑ j ∈ nonlinearDegrees N, (j : ℝ)*(j+2)*b j^2 := by
    apply sum_le_sum
    intro j hj
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast (mem_nonlinearDegrees.mp hj).1
    have hMul := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ j+2 by linarith only [hj']) (Nat.cast_nonneg (α := ℝ) j)
    calc
      _ = ((j : ℝ)*4)*b j^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMul (sq_nonneg (b j))
  rw [← mul_sum,← he] at hSum
  change (∑ j ∈ nonlinearDegrees N, (j : ℝ)*b j^2) ≤ 3/4
  linarith only [hSum,hI]

/-- The single-edge coefficient is chosen to make the squared coefficient mass one. -/
noncomputable def singleEdgeCoefficient (N : ℕ) : ℝ :=
  Real.sqrt (edgeWeight (nonlinearDegrees N) (bernsteinCoefficient N))

lemma singleEdgeCoefficient_pos {N : ℕ} (hN : 0 < N) : 0 < singleEdgeCoefficient N :=
  Real.sqrt_pos.mpr ((by norm_num : (0 : ℝ) < 5/8).trans_le
    (edgeWeight_ge (fun _ hj ↦ (mem_nonlinearDegrees.mp hj).1) (bernsteinCoefficient_energy hN)))

lemma singleEdgeCoefficient_sq {N : ℕ} (hN : 0 < N) :
    singleEdgeCoefficient N ^ 2 =
      1-semicircleAverage (fun x ↦ ((bernsteinAbsPolynomial N).eval x)^2) + bernsteinCoefficient N 0 ^ 2 := by
  have hP := sum_sq_semicircleCoefficient (bernsteinAbsPolynomial N) N (natDegree_bernsteinAbsPolynomial_le N)
  change _ = ∑ j ∈ range (N+1), bernsteinCoefficient N j ^ 2 at hP
  rw [sum_chebyshevDegrees hN,bernsteinCoefficient_one hN,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] at hP
  rw [singleEdgeCoefficient,Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 5/8).trans
    (edgeWeight_ge (fun _ hj ↦ (mem_nonlinearDegrees.mp hj).1) (bernsteinCoefficient_energy hN))),hP,edgeWeight]
  ring

/-- The mean absolute value under the semicircle law. -/
noncomputable def semicircleAbsoluteMean : ℝ := semicircleAverage abs

lemma semicircleAbsoluteMean_pos : 0 < semicircleAbsoluteMean := by
  have h₁ : semicircleAverage (fun x ↦ (1/2)*x^2) = 1/2 := by
    rw [semicircleAverage_const_mul,semicircleAverage_sq,mul_one]
  have h₂ : semicircleAverage (fun x ↦ (1/2)*x^2) ≤ semicircleAbsoluteMean := by
    apply semicircleAverage_mono (by fun_prop) continuous_abs
    intro x hx
    have h : |x| ≤ 2 := abs_le.mpr hx
    nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg x),sq_abs x]
  linarith only [h₁,h₂]

private lemma bernstein_mean_bounds {N : ℕ} (hN : 0 < N) :
    semicircleAbsoluteMean ≤ bernsteinCoefficient N 0 ∧
      bernsteinCoefficient N 0 ≤ semicircleAbsoluteMean+2/Real.sqrt N := by
  unfold bernsteinCoefficient semicircleAbsoluteMean
  rw [semicircleCoefficient_zero]
  constructor
  · exact semicircleAverage_mono continuous_abs (bernsteinAbsPolynomial N).continuous fun _ hx ↦
      (bernsteinAbsPolynomial_bounds hN.ne' hx).1
  · have h := semicircleAverage_mono (f := (bernsteinAbsPolynomial N).eval) (g := fun x ↦ |x|+2/Real.sqrt N)
      (bernsteinAbsPolynomial N).continuous (continuous_abs.add continuous_const)
      (fun x hx ↦ by linarith only [(bernsteinAbsPolynomial_bounds hN.ne' hx).2])
    rwa [semicircleAverage_add continuous_abs continuous_const,semicircleAverage_const] at h

lemma bernsteinCoefficient_zero_pos {N : ℕ} (hN : 0 < N) : 0 < bernsteinCoefficient N 0 :=
  semicircleAbsoluteMean_pos.trans_le (bernstein_mean_bounds hN).1

private lemma bernstein_sq_mean_bounds {N : ℕ} (hN : 0 < N) :
    let e := 2/Real.sqrt N
    1 ≤ semicircleAverage (fun x ↦ ((bernsteinAbsPolynomial N).eval x)^2) ∧
      semicircleAverage (fun x ↦ ((bernsteinAbsPolynomial N).eval x)^2) ≤ 1+e*(4+e) := by
  let e := 2/Real.sqrt N
  let R := (bernsteinAbsPolynomial N).eval
  have hE : 0 ≤ e := by unfold e; positivity
  have hR : Continuous R := (bernsteinAbsPolynomial N).continuous
  have hX : Continuous (fun x : ℝ ↦ x^2) := by fun_prop
  constructor
  · rw [← semicircleAverage_sq]
    exact semicircleAverage_mono hX (hR.pow 2) fun x hx ↦
      (sq_abs x).ge.trans (pow_le_pow_left₀ (abs_nonneg _) (bernsteinAbsPolynomial_bounds hN.ne' hx).1 2)
  · have hPoint (x : ℝ) (hx : x ∈ Set.Icc (-2) 2) : R x^2 ≤ x^2+e*(4+e) := by
      obtain ⟨h₁,h₂⟩ := bernsteinAbsPolynomial_bounds hN.ne' hx
      change R x-|x| ≤ e at h₂
      have hx' := abs_le.mpr hx
      have h₃ : R x+|x| ≤ 4+e := by linarith only [h₂,hx']
      have h₄ : 0 ≤ R x+|x| := add_nonneg ((abs_nonneg x).trans h₁) (abs_nonneg x)
      have h' := mul_le_mul h₂ h₃ h₄ hE
      nlinarith only [h',sq_abs x]
    have h : semicircleAverage (fun x ↦ R x^2) ≤ semicircleAverage (fun x ↦ x^2+e*(4+e)) :=
      semicircleAverage_mono (hR.pow 2) (hX.add continuous_const) hPoint
    rwa [semicircleAverage_add hX continuous_const,semicircleAverage_sq,semicircleAverage_const] at h

/-- The single-edge coefficient and the constant coefficient become equal in the limit. -/
theorem tendsto_singleEdgeCoefficient_div_bernsteinCoefficient :
    Tendsto (fun m : ℕ ↦ singleEdgeCoefficient (m+2)/bernsteinCoefficient (m+2) 0) atTop (𝓝 1) := by
  let e (m : ℕ) := 2/Real.sqrt (m+2 : ℕ)
  let b (m : ℕ) := bernsteinCoefficient (m+2) 0
  let r (m : ℕ) := semicircleAverage (fun x ↦ ((bernsteinAbsPolynomial (m+2)).eval x)^2)
  have hS := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have he : Tendsto e atTop (𝓝 0) := tendsto_const_nhds.div_atTop hS
  have hb : Tendsto b atTop (𝓝 semicircleAbsoluteMean) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun m ↦ semicircleAbsoluteMean+e m) atTop (𝓝 semicircleAbsoluteMean) by
        simpa only [add_zero] using tendsto_const_nhds.add he)
    · exact Eventually.of_forall fun m ↦ (bernstein_mean_bounds (show 0 < m+2 by omega)).1
    · exact Eventually.of_forall fun m ↦ (bernstein_mean_bounds (show 0 < m+2 by omega)).2
  have hr : Tendsto r atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun m ↦ 1+e m*(4+e m)) atTop (𝓝 1) by
        simpa only [add_zero,zero_mul] using tendsto_const_nhds.add (he.mul (tendsto_const_nhds.add he)))
    · exact Eventually.of_forall fun m ↦ (bernstein_sq_mean_bounds (show 0 < m+2 by omega)).1
    · exact Eventually.of_forall fun m ↦ (bernstein_sq_mean_bounds (show 0 < m+2 by omega)).2
  have ha : Tendsto (fun m : ℕ ↦ singleEdgeCoefficient (m+2)) atTop (𝓝 semicircleAbsoluteMean) := by
    have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := ((hOne.sub hr).add (hb.pow 2)).sqrt
    simp only [sub_self,zero_add,Real.sqrt_sq semicircleAbsoluteMean_pos.le] at h
    refine h.congr' (Eventually.of_forall fun m ↦ ?_)
    change Real.sqrt (1-r m+b m^2) = singleEdgeCoefficient (m+2)
    rw [← singleEdgeCoefficient_sq (show 0 < m+2 by omega),
      Real.sqrt_sq (singleEdgeCoefficient_pos (show 0 < m+2 by omega)).le]
  change Tendsto ((fun m ↦ singleEdgeCoefficient (m+2))/b) atTop (𝓝 1)
  simpa only [div_self semicircleAbsoluteMean_pos.ne'] using ha.div hb semicircleAbsoluteMean_pos.ne'

end LovaszTheta.Independent
