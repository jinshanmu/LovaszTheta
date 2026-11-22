module

public import LovaszTheta.Fourier
public import LovaszTheta.Signs

/-!
# Real cyclic character moments

At regular frequencies the cosine product averages to one half
exactly when the frequencies agree up to sign.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- A frequency is regular when it is distinct from its additive inverse. -/
def RegularFrequency (k : ZMod n) : Prop := 2*k ≠ 0

lemma re_stdAddChar_neg (a : ZMod n) :
    (ZMod.stdAddChar (-a)).re = (ZMod.stdAddChar a).re := by
  rw [← star_stdAddChar, Complex.star_def, Complex.conj_re]

private lemma re_stdAddChar_mul_re (a b : ZMod n) :
    (ZMod.stdAddChar a).re * (ZMod.stdAddChar b).re =
      ((ZMod.stdAddChar (a+b)).re + (ZMod.stdAddChar (a-b)).re) / 2 := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← star_stdAddChar b]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma sum_re_stdAddChar_mul (a : ZMod n) :
    (∑ r, (ZMod.stdAddChar (a*r)).re) = if a = 0 then (n : ℝ) else 0 := by
  rw [← Complex.re_sum, sum_stdAddChar_mul]
  split_ifs <;> simp

/-- The mean of the product of two real characters at a regular frequency. -/
theorem average_re_stdAddChar_pair (k j : ZMod n) (hk : RegularFrequency k) :
    average (fun r : ZMod n ↦ (ZMod.stdAddChar (-(r*k))).re * (ZMod.stdAddChar (-(r*j))).re) =
      if j = k ∨ j = -k then 1 / 2 else 0 := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hsum : (∑ r : ZMod n, (ZMod.stdAddChar (k*r)).re * (ZMod.stdAddChar (j*r)).re) =
      ((if k+j = 0 then (n : ℝ) else 0) + (if k-j = 0 then (n : ℝ) else 0)) / 2 := by
    simp_rw [re_stdAddChar_mul_re, ← add_mul, ← sub_mul]
    rw [← sum_div, sum_add_distrib, sum_re_stdAddChar_mul, sum_re_stdAddChar_mul]
  have hPlus : k+j = 0 ↔ j = -k := by
    rw [add_comm k j, ← eq_neg_iff_add_eq_zero]
  have hMinus : k-j = 0 ↔ j = k := sub_eq_zero.trans eq_comm
  have hNo : k ≠ -k := by
    intro he
    apply hk
    rw [two_mul]
    exact (congrArg (fun z ↦ k+z) he).trans (add_neg_cancel k)
  simp only [average, ZMod.card, re_stdAddChar_neg, mul_comm _ k, mul_comm _ j]
  rw [hsum]
  simp only [hPlus, hMinus]
  by_cases hE : j = k
  · have hOther : j ≠ -k := hE.symm ▸ hNo
    rw [ite_eq_right hOther, ite_eq_left hE, ite_eq_left (Or.inl hE), zero_add]
    field_simp
  · by_cases hO : j = -k
    · rw [ite_eq_left hO, ite_eq_right hE, ite_eq_left (Or.inr hO), add_zero]
      field_simp
    · simp [hE, hO]

end LovaszTheta.Circulant
