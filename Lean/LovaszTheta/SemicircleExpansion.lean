module

public import LovaszTheta.SemicircleChebyshev

/-!
# Chebyshev expansions and the derivative energy

Finite Chebyshev expansions are unique by semicircle
orthogonality. The weighted derivative energy is the squared
coefficient sum with weights j(j+2).
-/

@[expose] public section

open Finset Polynomial Real Set
open scoped Polynomial

namespace LovaszTheta.Independent

lemma semicircleAverage_const_mul (a : ℝ) (f : ℝ → ℝ) :
    semicircleAverage (fun x ↦ a*f x) = a*semicircleAverage f := by
  unfold semicircleAverage
  simp only [mul_assoc,intervalIntegral.integral_const_mul]
  ring

lemma semicircleAverage_sum {I : Type*} (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    semicircleAverage (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, semicircleAverage (f i) := by
  unfold semicircleAverage
  simp_rw [sum_mul]
  have hInt (i : I) (hi : i ∈ s) :
      IntervalIntegrable (fun t : ℝ ↦ f i (2*cos t)*(sin t)^2) MeasureTheory.volume 0 π :=
    (((hf i hi).comp (continuous_cos.const_mul _)).mul (continuous_sin.pow _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hInt,mul_sum]

lemma semicircleAverage_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    semicircleAverage (fun x ↦ f x+g x) = semicircleAverage f+semicircleAverage g := by
  unfold semicircleAverage
  simp_rw [add_mul]
  have hInt (u : ℝ → ℝ) (hu : Continuous u) :
      IntervalIntegrable (fun t : ℝ ↦ u (2*cos t)*(sin t)^2) MeasureTheory.volume 0 π :=
    (((hu.comp (continuous_cos.const_mul _)).mul (continuous_sin.pow _)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hInt f hf) (hInt g hg),mul_add]

lemma semicircleAverage_const (a : ℝ) : semicircleAverage (fun _ ↦ a) = a := by
  simpa only [mul_one,semicircleAverage_one] using semicircleAverage_const_mul a (fun _ ↦ 1)

lemma semicircleAverage_neg_input (f : ℝ → ℝ) :
    semicircleAverage (fun x ↦ f (-x)) = semicircleAverage f := by
  let F (t : ℝ) := f (2*cos t)*(sin t)^2
  have he (t : ℝ) : f (-(2*cos t))*(sin t)^2 = F (π-t) := by
    simp only [F,cos_pi_sub,sin_pi_sub,mul_neg]
  unfold semicircleAverage
  simp_rw [he,intervalIntegral.integral_comp_sub_left F π,sub_self,sub_zero]
  rfl

lemma semicircleAverage_of_odd {f : ℝ → ℝ} (hf : f.Odd) : semicircleAverage f = 0 := by
  have h := semicircleAverage_neg_input f
  rw [show (fun x ↦ f (-x)) = (fun x ↦ -f x) from funext hf] at h
  have hn : semicircleAverage (fun x ↦ -f x) = -semicircleAverage f := by
    simpa only [neg_one_mul] using semicircleAverage_const_mul (-1) f
  linarith only [h,hn]

/-- The coefficient of a Chebyshev polynomial under the semicircle integral. -/
noncomputable def semicircleCoefficient (p : ℝ[X]) (j : ℕ) : ℝ :=
  semicircleAverage (fun x ↦ p.eval x*(semicircleChebyshev j).eval x)

private lemma exists_chebyshev_expansion (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N) :
    ∃ b : ℕ → ℝ, p = ∑ j ∈ range (N+1), C (b j)*semicircleChebyshev j := by
  classical
  let S : Polynomial.Sequence ℝ :=
    ⟨semicircleChebyshev, fun j ↦ by
      rw [degree_eq_natDegree (monic_semicircleChebyshev j).ne_zero,natDegree_semicircleChebyshev]⟩
  have hSpan : p ∈ Submodule.span ℝ (S '' Set.Iio (N+1)) := by
    rw [S.span_degreeLT (fun j _ ↦ show IsUnit (semicircleChebyshev j).leadingCoeff by
      rw [(monic_semicircleChebyshev j).leadingCoeff]; exact isUnit_one),mem_degreeLT]
    exact degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (hN.trans_lt (Nat.lt_succ_self _)))
  obtain ⟨b,hb,h⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hSpan
  change (↑b.support : Set ℕ) ⊆ Set.Iio (N+1) at hb
  have hB : b.support ⊆ range (N+1) := by
    intro i hi
    exact mem_range.mpr (hb hi)
  rw [Finsupp.linearCombination_apply,Finsupp.sum_of_support_subset b hB (fun i a ↦ a • S i)
    (fun _ _ ↦ zero_smul _ _)] at h
  exact ⟨b,by simpa only [Polynomial.smul_eq_C_mul] using h.symm⟩

lemma semicircleCoefficient_of_expansion (p : ℝ[X]) (s : Finset ℕ) (b : ℕ → ℝ)
    (h : p = ∑ j ∈ s, C (b j)*semicircleChebyshev j) (i : ℕ) :
    semicircleCoefficient p i = if i ∈ s then b i else 0 := by
  classical
  unfold semicircleCoefficient
  simp_rw [h,eval_finsetSum,eval_mul,eval_C,sum_mul,mul_assoc]
  let f (j : ℕ) (x : ℝ) := b j*((semicircleChebyshev j).eval x*(semicircleChebyshev i).eval x)
  have hf (j : ℕ) : Continuous (f j) :=
    (((semicircleChebyshev j).continuous).mul (semicircleChebyshev i).continuous).const_mul _
  change semicircleAverage (fun x ↦ ∑ j ∈ s, f j x) = _
  rw [semicircleAverage_sum s f (fun j _ ↦ hf j)]
  unfold f
  simp_rw [semicircleAverage_const_mul,semicircleAverage_chebyshev_mul,mul_ite,mul_one,mul_zero]
  exact sum_ite_eq' _ _ _

/-- The coefficients recovered by integration give the finite expansion. -/
theorem chebyshev_expansion (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N) :
    p = ∑ j ∈ range (N+1), C (semicircleCoefficient p j)*semicircleChebyshev j := by
  obtain ⟨b,h⟩ := exists_chebyshev_expansion p N hN
  exact h.trans (sum_congr rfl fun i hi ↦ by
    rw [semicircleCoefficient_of_expansion p _ b h,ite_eq_left hi])

lemma semicircleCoefficient_zero (p : ℝ[X]) :
    semicircleCoefficient p 0 = semicircleAverage p.eval := by
  simp only [semicircleCoefficient,semicircleChebyshev_zero,eval_one,mul_one]

lemma semicircleCoefficient_one_of_even (p : ℝ[X]) (hp : p.eval.Even) :
    semicircleCoefficient p 1 = 0 := by
  simp only [semicircleCoefficient,semicircleChebyshev_one,eval_X]
  apply semicircleAverage_of_odd
  intro x
  change p.eval (-x)*(-x) = -(p.eval x*x)
  rw [show p.eval (-x) = p.eval x from hp x,mul_neg]

/-- Parseval's identity on polynomials for the semicircle law. -/
theorem sum_sq_semicircleCoefficient (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N) :
    semicircleAverage (fun x ↦ (p.eval x)^2) = ∑ j ∈ range (N+1), semicircleCoefficient p j ^ 2 := by
  let c := semicircleCoefficient p
  have he (x : ℝ) : p.eval x ^ 2 =
      ∑ j ∈ range (N+1), c j*(p.eval x*(semicircleChebyshev j).eval x) := by
    conv_lhs => rw [pow_two]
    conv_lhs => enter [2]; rw [chebyshev_expansion p N hN]
    simp only [eval_finsetSum,eval_mul,eval_C,mul_sum]
    exact sum_congr rfl (fun j _ ↦ by ring)
  simp_rw [he]
  let f (j : ℕ) (x : ℝ) := c j*(p.eval x*(semicircleChebyshev j).eval x)
  have hf (j : ℕ) : Continuous (f j) :=
    (p.continuous.mul (semicircleChebyshev j).continuous).const_mul _
  change semicircleAverage (fun x ↦ ∑ j ∈ range (N+1), f j x) = _
  rw [semicircleAverage_sum _ f (fun j _ ↦ hf j)]
  simp only [f,semicircleAverage_const_mul]
  change (∑ j ∈ range (N+1), c j*c j) = _
  simp only [← pow_two,c]

/-- Energy of the derivative in the semicircle weight. -/
theorem semicircleAverage_derivative_energy (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N) :
    semicircleAverage (fun x ↦ (4-x^2)*(p.derivative.eval x)^2) =
      ∑ j ∈ range (N+1), (j : ℝ)*(j+2)*semicircleCoefficient p j ^ 2 := by
  let c := semicircleCoefficient p
  have he (x : ℝ) : (4-x^2)*(p.derivative.eval x)^2 =
      ∑ j ∈ range (N+1), c j*((4-x^2)*p.derivative.eval x*(semicircleChebyshev j).derivative.eval x) := by
    conv_lhs => rw [pow_two (p.derivative.eval x),← mul_assoc]
    conv_lhs => enter [2]; rw [chebyshev_expansion p N hN]
    simp only [map_sum,derivative_mul,derivative_C,zero_mul,zero_add,eval_finsetSum,eval_mul,eval_C,mul_sum]
    exact sum_congr rfl (fun j _ ↦ by ring)
  simp_rw [he]
  have hCont (j : ℕ) : Continuous
      (fun x ↦ (4-x^2)*p.derivative.eval x*(semicircleChebyshev j).derivative.eval x) :=
    ((by fun_prop : Continuous (fun x : ℝ ↦ 4-x^2)).mul p.derivative.continuous).mul
      (semicircleChebyshev j).derivative.continuous
  let f (j : ℕ) (x : ℝ) := c j*((4-x^2)*p.derivative.eval x*(semicircleChebyshev j).derivative.eval x)
  have hf (j : ℕ) : Continuous (f j) := (hCont j).const_mul _
  change semicircleAverage (fun x ↦ ∑ j ∈ range (N+1), f j x) = _
  rw [semicircleAverage_sum _ f (fun j _ ↦ hf j)]
  simp only [f,semicircleAverage_const_mul,semicircleAverage_derivative_mul_chebyshev]
  change (∑ j ∈ range (N+1), c j*((j : ℝ)*(j+2)*c j)) = _
  exact sum_congr rfl (fun j _ ↦ by unfold c; ring)

end LovaszTheta.Independent
