module

public import LovaszTheta.IsolatedExtension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scalar from isolated labels

The falling factorial for the discarded labels differs from the
corresponding power by a relative error of order (1/n).
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

private lemma one_sub_prod_one_sub_le_sum {I : Type*} (s : Finset I) (f : I → ℝ)
    (h₀ : ∀ i ∈ s, 0 ≤ f i) (h₁ : ∀ i ∈ s, f i ≤ 1) :
    1-(∏ i ∈ s, (1-f i)) ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi,sum_insert hi]
    have h0 := h₀ i (mem_insert_self _ _)
    have h1 := h₁ i (mem_insert_self _ _)
    have h0s (j : I) (hj : j ∈ s) := h₀ j (mem_insert_of_mem hj)
    have h1s (j : I) (hj : j ∈ s) := h₁ j (mem_insert_of_mem hj)
    have hSum : 0 ≤ ∑ j ∈ s, f j := sum_nonneg h0s
    calc
      _ = f i+(1-f i)*(1-(∏ j ∈ s, (1-f j))) := by ring
      _ ≤ f i+(1-f i)*(∑ j ∈ s, f j) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (ih h0s h1s) (sub_nonneg.mpr h1))
      _ ≤ _ := add_le_add (le_refl _) (mul_le_of_le_one_left hSum (show 1-f i ≤ 1 by linarith))

/-- Uniform relative error for the extension factor with a fixed retained and discarded size. -/
theorem abs_descFactorial_sub_pow_le {n q z : ℕ} (hn : 0 < n) (hSize : q+z ≤ n) :
    |((n-q).descFactorial z : ℝ) - (n : ℝ)^z| ≤
      ((z : ℝ)*(q+z))*(n : ℝ)^((z : ℝ)-1) := by
  have hPos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let f (i : ℕ) := ((q : ℝ)+i)/(n : ℝ)
  have h₀ (i : ℕ) (_ : i ∈ range z) : 0 ≤ f i := by unfold f; positivity
  have h₁ (i : ℕ) (hi : i ∈ range z) : f i ≤ 1 := by
    apply (div_le_one hPos).mpr
    have hI := mem_range.mp hi
    exact_mod_cast (show q+i ≤ n by omega)
  have hFactor : ((n-q).descFactorial z : ℝ) = (n : ℝ)^z * ∏ i ∈ range z, (1-f i) := by
    have hPow : (∏ _i ∈ range z, (n : ℝ)) = (n : ℝ)^z := by rw [prod_const,card_range]
    rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod,← hPow,← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hI := mem_range.mp hi
    rw [Nat.cast_sub (by omega : i ≤ n-q),Nat.cast_sub (by omega : q ≤ n)]
    unfold f
    field_simp
    ring
  have hProd : (∏ i ∈ range z, (1-f i)) ≤ 1 :=
    prod_le_one₀ (fun i hi ↦ sub_nonneg.mpr (h₁ i hi)) (fun i hi ↦ by linarith [h₀ i hi])
  rw [hFactor,show (n : ℝ)^z * (∏ i ∈ range z, (1-f i)) - (n : ℝ)^z =
    (n : ℝ)^z * ((∏ i ∈ range z, (1-f i))-1) by ring,abs_mul,abs_of_nonneg (by positivity),
    abs_of_nonpos (sub_nonpos.mpr hProd)]
  have hLimit (i : ℕ) (hi : i ∈ range z) : f i ≤ ((q : ℝ)+z)/(n : ℝ) := by
    have hi' : (i : ℝ) ≤ z := by exact_mod_cast (mem_range.mp hi).le
    exact div_le_div_of_nonneg_right (by linarith) hPos.le
  have hSum : (∑ i ∈ range z, f i) ≤ (z : ℝ)*((q : ℝ)+z)/(n : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ range z, ((q : ℝ)+z)/(n : ℝ) := sum_le_sum hLimit
      _ = _ := by rw [sum_const,card_range,nsmul_eq_mul]; ring
  have hPow (m : ℕ) : (n : ℝ)^((m : ℝ)-1) = (n : ℝ)^m/(n : ℝ) := by
    rw [Real.rpow_sub hPos,Real.rpow_natCast,Real.rpow_one]
  calc
    _ = (n : ℝ)^z * (1-∏ i ∈ range z, (1-f i)) := by ring
    _ ≤ (n : ℝ)^z * ((z : ℝ)*((q : ℝ)+z)/(n : ℝ)) :=
      mul_le_mul_of_nonneg_left ((one_sub_prod_one_sub_le_sum _ _ h₀ h₁).trans hSum) (by positivity)
    _ = _ := by rw [hPow]; ring

end LovaszTheta.Independent
