module

public import LovaszTheta.Signs
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The two-point moment inequality

The even terms in the binomial expansion of the two sign values are
bounded coefficient by coefficient by the expansion of the quadratic
form in the hypercontractive estimate.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

private lemma choose_even_le (m j : ℕ) :
    (2*m).choose (2*j) ≤ m.choose j * (2*m-1)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j < m
    · let c := 2*m-1
      have hStep : 2*(j+1) = 2*j+1+1 := by omega
      have hDoubleSub : 2*m-2*j = 2*(m-j) := by omega
      have hC : 2*m-(2*j+1) ≤ (2*j+1)*c := by
        exact (show 2*m-(2*j+1) ≤ c by dsimp [c]; omega).trans (Nat.le_mul_of_pos_left _ (by omega))
      refine Nat.le_of_mul_le_mul_right (c := (2*(j+1))*(2*j+1)) ?_ (by positivity)
      calc
        _ = ((2*m).choose (2*j) * (2*(m-j))) * (2*m-(2*j+1)) := by
          rw [hStep, ← Nat.mul_assoc, Nat.choose_succ_right_eq, mul_right_comm,
            Nat.choose_succ_right_eq, hDoubleSub]
        _ ≤ (m.choose j * c^j * (2*(m-j))) * ((2*j+1)*c) := by gcongr
        _ = (m.choose j * (m-j)) * (c^j * c * (2*(2*j+1))) := by ring
        _ = _ := by
          rw [← Nat.choose_succ_right_eq, pow_succ]
          change m.choose (j+1) * (j+1) * (c^j * c * (2*(2*j+1))) =
            m.choose (j+1) * (c^j*c) * (2*(j+1)*(2*j+1))
          ring
    · rw [Nat.choose_eq_zero_of_lt (show 2*m < 2*(j+1) by omega)]
      exact Nat.zero_le _

private lemma sum_even_binomial (a b : ℝ) (m : ℕ) :
    ((a+b)^(2*m)+(a-b)^(2*m))/2 =
      ∑ j ∈ range (m+1), b^(2*j) * a^(2*(m-j)) * ((2*m).choose (2*j) : ℝ) := by
  calc
    _ = ∑ i ∈ range (2*m+1),
        if Even i then b^i * a^(2*m-i) * ((2*m).choose i : ℝ) else 0 := by
      rw [add_comm a b, sub_eq_add_neg, add_comm a (-b), add_pow, add_pow,
        ← sum_add_distrib, sum_div]
      apply sum_congr rfl
      intro i _
      have hn : (-b)^i = ((-1 : ℝ)^i) * b^i := by rw [← mul_pow, neg_one_mul]
      rw [hn, neg_one_pow_eq_ite]
      split_ifs <;> ring
    _ = _ := by
      rw [← sum_filter]
      symm
      refine sum_bij (fun j _ ↦ 2*j) ?_ ?_ ?_ ?_
      · intro j hj
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hj; omega), even_two_mul j⟩
      · intro j _ i _ h
        omega
      · intro i hi
        obtain ⟨hb, k, hk⟩ := mem_filter.mp hi
        exact ⟨k, mem_range.mpr (by have := mem_range.mp hb; omega), by omega⟩
      · intro j _
        rw [show 2*m-2*j = 2*(m-j) by omega]

/-- The scalar even moment of two sign values is bounded by a quadratic
form raised to half the moment order. -/
theorem twoPoint_even_moment_le (a b : ℝ) (m : ℕ) :
    ((a+b)^(2*m)+(a-b)^(2*m))/2 ≤ (a^2 + ((2*m-1 : ℕ) : ℝ)*b^2)^m := by
  rw [sum_even_binomial, add_comm (a^2), add_pow]
  apply sum_le_sum
  intro j _
  rw [pow_mul b, pow_mul a, mul_pow]
  have hChoose : ((2*m).choose (2*j) : ℝ) ≤ (m.choose j : ℝ) * ((2*m-1 : ℕ) : ℝ)^j := by
    exact_mod_cast choose_even_le m j
  calc
    _ ≤ (b^2)^j * (a^2)^(m-j) * ((m.choose j : ℝ) * ((2*m-1 : ℕ) : ℝ)^j) :=
      mul_le_mul_of_nonneg_left hChoose (by positivity)
    _ = _ := by ring

end LovaszTheta.Circulant
