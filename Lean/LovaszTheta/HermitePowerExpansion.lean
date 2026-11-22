module

public import LovaszTheta.HermiteMoments
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Power expansion of the Hermite products

The monic probabilists' Hermite polynomial has its stated
factorial normalization in the highest power. The finite
power expansion keeps track of the exponents in each factor.
-/

@[expose] public section

open Finset Polynomial
open scoped Classical Polynomial

namespace LovaszTheta.Circulant

lemma natDegree_realHermite (j : ℕ) : (realHermite j).natDegree = j := by
  rw [realHermite,natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),natDegree_hermite]

lemma coeff_realHermite_self (j : ℕ) : (realHermite j).coeff j = 1 := by
  simp [realHermite,coeff_hermite_self]

/-- The power coefficient of the normalized Hermite polynomial. -/
noncomputable def hermitePowerCoeff (j r : ℕ) : ℝ :=
  (realHermite j).coeff r / Real.sqrt j.factorial

lemma hermitePowerCoeff_self (j : ℕ) :
    hermitePowerCoeff j j = (Real.sqrt j.factorial)⁻¹ := by
  simp [hermitePowerCoeff, coeff_realHermite_self,one_div]

lemma normalizedHermite_eq_sum_powers (j : ℕ) (x : ℝ) :
    normalizedHermite j x = ∑ r : Fin (j+1), hermitePowerCoeff j r.val * x^r.val := by
  have he := (realHermite j).as_sum_range_C_mul_X_pow' (by rw [natDegree_realHermite]; omega : (realHermite j).natDegree < j+1)
  have h : (realHermite j).eval x = ∑ i ∈ range (j+1), (realHermite j).coeff i*x^i := by
    calc
      _ = (∑ i ∈ range (j+1), C ((realHermite j).coeff i)*X^i).eval x := congrArg (eval x) he
      _ = _ := by
        change (evalRingHom x) (∑ i ∈ range (j+1), C ((realHermite j).coeff i)*X^i) = _
        rw [map_sum]
        exact sum_congr rfl fun i _ ↦ by
          change (C ((realHermite j).coeff i)*X^i).eval x = _
          simp only [eval_mul,eval_C,eval_pow,eval_X]
  rw [normalizedHermite,h,sum_div,Finset.sum_range]
  exact sum_congr rfl fun _ _ ↦ by unfold hermitePowerCoeff; ring

variable {I : Type*} (m : I →₀ ℕ)

/-- The tuples of exponents up to the degrees of the prescribed product. -/
abbrev HermitePowerTuple := ∀ i : m.support, Fin (m i.val+1)

/-- The tuple taking the leading power in every factor. -/
def leadingHermitePowerTuple : HermitePowerTuple m :=
  fun i ↦ ⟨m i.val,Nat.lt_succ_self _⟩

/-- The coefficient of an exponent tuple after expanding each Hermite factor. -/
noncomputable def hermiteProductPowerCoeff (q : HermitePowerTuple m) : ℝ :=
  ∏ i : m.support, hermitePowerCoeff (m i.val) (q i).val

lemma hermiteProductPowerCoeff_leading :
    hermiteProductPowerCoeff m (leadingHermitePowerTuple m) =
      (∏ i : m.support, Real.sqrt (m i.val).factorial)⁻¹ := by
  simp only [hermiteProductPowerCoeff,leadingHermitePowerTuple,hermitePowerCoeff_self,prod_inv_distrib]

theorem prod_normalizedHermite_eq_sum_powers (x : I → ℝ) :
    (∏ i ∈ m.support, normalizedHermite (m i) (x i)) =
      ∑ q : HermitePowerTuple m, hermiteProductPowerCoeff m q * ∏ i : m.support, x i.val^(q i).val := by
  rw [← prod_coe_sort m.support (fun i ↦ normalizedHermite (m i) (x i))]
  simp only [normalizedHermite_eq_sum_powers]
  rw [Fintype.prod_sum]
  exact sum_congr rfl fun q _ ↦ prod_mul_distrib

private lemma sum_abs_realHermite_coeff_le (j : ℕ) :
    (∑ r ∈ range (j+1), |(realHermite j).coeff r|) ≤ j.factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    let p := realHermite j
    let A := ∑ r ∈ range (j+1), |p.coeff r|
    have hX : (∑ r ∈ range (j+1+1), |(X*p).coeff r|) = A := by
      rw [sum_range_succ']
      simp only [coeff_X_mul, coeff_X_mul_zero, abs_zero, add_zero, A]
    have hD₀ : (∑ r ∈ range j, |p.derivative.coeff r|) =
        ∑ r ∈ range (j+1+1), |p.derivative.coeff r| := by
      refine sum_subset (range_mono (by omega)) ?_
      intro r hr hn
      have hR : j ≤ r := Nat.le_of_not_gt (fun he ↦ hn (mem_range.mpr he))
      rw [coeff_derivative, coeff_eq_zero_of_natDegree_lt, zero_mul, abs_zero]
      unfold p
      rw [natDegree_realHermite]
      omega
    have hD : (∑ r ∈ range (j+1+1), |p.derivative.coeff r|) ≤ j*A := by
      rw [← hD₀]
      calc
        _ ≤ ∑ r ∈ range j, (j : ℝ)*|p.coeff (r+1)| := by
          apply sum_le_sum
          intro r hr
          rw [coeff_derivative, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ)+1), mul_comm]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hr)) (abs_nonneg _)
        _ ≤ _ := by
          rw [← mul_sum]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          unfold A
          rw [sum_range_succ']
          exact le_add_of_nonneg_right (abs_nonneg _)
    calc
      _ ≤ ∑ r ∈ range (j+1+1), (|(X*p).coeff r|+|p.derivative.coeff r|) := by
        rw [realHermite_succ]
        exact sum_le_sum fun r _ ↦ by rw [coeff_sub]; exact abs_sub _ _
      _ ≤ A+j*A := by
        rw [sum_add_distrib,hX]
        exact add_le_add_right hD A
      _ = ((j+1 : ℕ) : ℝ)*A := by push_cast; ring
      _ ≤ _ := by
        rw [Nat.factorial_succ,Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left ih (by positivity)

/-- The absolute mass of the normalized Hermite power coefficients is at most the factorial. -/
theorem sum_abs_hermitePowerCoeff_le (j : ℕ) :
    (∑ r : Fin (j+1), |hermitePowerCoeff j r.val|) ≤ j.factorial := by
  have h₀ : 1 ≤ Real.sqrt (j.factorial : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.factorial_pos j)
  calc
    _ ≤ ∑ r : Fin (j+1), |(realHermite j).coeff r.val| := by
      apply sum_le_sum
      intro r _
      rw [hermitePowerCoeff,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_self (abs_nonneg _) h₀
    _ ≤ _ := by
      exact (Finset.sum_range (n := j+1) (fun r ↦ |(realHermite j).coeff r|)).symm.le.trans
        (sum_abs_realHermite_coeff_le j)

end LovaszTheta.Circulant
