module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Tactic

/-!
# Polynomial and coefficient estimates for the independent-edge certificate

The Bernstein polynomial of the absolute value gives a nonnegative
certificate polynomial after adding the identity function. The
Chebyshev coefficient energy bound also gives the contraction of
the squared coefficient masses at successive construction depths.
-/

@[expose] public section

open Finset Filter
open scoped Polynomial Topology unitInterval

namespace LovaszTheta.Independent

/-- The Bernstein approximation to the absolute value on the interval
parametrized by x = 4t - 2. -/
noncomputable def bernsteinAbs (N : ℕ) (t : I) : ℝ :=
  ∑ j : Fin (N + 1), bernstein N j t * |4 * (bernstein.z j : ℝ) - 2|

private lemma bernstein_mean {N : ℕ} (hN : N ≠ 0) (t : I) :
    (∑ j : Fin (N + 1), bernstein N j t * (bernstein.z j : ℝ)) = (t : ℝ) := by
  have h := congrArg (Polynomial.evalRingHom (t : ℝ)) (bernsteinPolynomial.sum_smul ℝ N)
  have h' : (∑ j : Fin (N + 1), (j : ℝ) * bernstein N j t) = (N : ℝ) * t := by
    simpa [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, Finset.sum_range,
      map_sum, nsmul_eq_mul] using h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [bernstein.z]
  calc
    _ = (∑ j : Fin (N + 1), (j : ℝ) * bernstein N j t) / N := by
      rw [Finset.sum_div]
      exact sum_congr rfl fun j _ ↦ by ring
    _ = _ := by rw [h', mul_comm, mul_div_cancel_right₀ _ hN']

/-- Jensen's inequality gives the pointwise lower bound by the absolute value. -/
theorem abs_le_bernsteinAbs {N : ℕ} (hN : N ≠ 0) (t : I) :
    |4 * (t : ℝ) - 2| ≤ bernsteinAbs N t := by
  have hMean : (∑ j : Fin (N + 1), bernstein N j t * (4 * (bernstein.z j : ℝ) - 2)) =
      4 * (t : ℝ) - 2 := by
    simp only [mul_sub, sum_sub_distrib, mul_left_comm (bernstein N _ t) 4,
      ← mul_sum, mul_comm (bernstein N _ t) 2, bernstein_mean hN, bernstein.probability,
      mul_one]
  rw [← hMean]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun j _ ↦ by
    rw [abs_mul, abs_of_nonneg bernstein_nonneg])

/-- The variance bound gives the uniform error in the manuscript. -/
theorem bernsteinAbs_sub_abs_le {N : ℕ} (hN : N ≠ 0) (t : I) :
    bernsteinAbs N t - |4 * (t : ℝ) - 2| ≤ 2 / Real.sqrt N := by
  let W := fun j : Fin (N + 1) ↦ bernstein N j t
  let z := fun j : Fin (N + 1) ↦ (bernstein.z j : ℝ)
  let x := (t : ℝ)
  have hN' : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hW (j : Fin (N + 1)) : 0 ≤ W j := bernstein_nonneg
  have hWT : ∑ j, W j = 1 := bernstein.probability _ _
  have hCauchy : (∑ j, W j * |x - z j|) ≤ Real.sqrt (x * (1 - x) / N) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin (N + 1)))
      (fun j ↦ Real.sqrt (W j)) (fun j ↦ Real.sqrt (W j) * |x - z j|)
    have hLeft (j : Fin (N + 1)) :
        Real.sqrt (W j) * (Real.sqrt (W j) * |x - z j|) = W j * |x - z j| := by
      rw [← mul_assoc, Real.mul_self_sqrt (hW j)]
    have hRight (j : Fin (N + 1)) :
        (Real.sqrt (W j) * |x - z j|) ^ 2 = (x - z j) ^ 2 * W j := by
      rw [mul_pow, Real.sq_sqrt (hW j), sq_abs, mul_comm]
    simp_rw [hLeft, Real.sq_sqrt (hW _), hRight] at h
    rw [hWT, Real.sqrt_one, one_mul] at h
    exact h.trans_eq (congrArg Real.sqrt (bernstein.variance hN t))
  have hPoint (j : Fin (N + 1)) :
      |4 * z j - 2| - |4 * x - 2| ≤ 4 * |x - z j| := by
    calc
      _ ≤ |(4 * z j - 2) - (4 * x - 2)| :=
        (le_abs_self _).trans (abs_abs_sub_abs_le_abs_sub _ _)
      _ = _ := by
        rw [show (4 * z j - 2) - (4 * x - 2) = 4 * (z j - x) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_sub_comm]
  have hErr : bernsteinAbs N t - |4 * x - 2| ≤ 4 * (∑ j, W j * |x - z j|) := by
    have hSum : (∑ j, W j * |4 * x - 2|) = |4 * x - 2| := by rw [← sum_mul, hWT, one_mul]
    change (∑ j, W j * |4 * z j - 2|) - |4 * x - 2| ≤ _
    rw [← hSum, ← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro j _
    rw [← mul_sub, mul_left_comm 4]
    exact mul_le_mul_of_nonneg_left (hPoint j) (hW j)
  have hVar : x * (1 - x) / N ≤ (1 / 4) / N :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x - 1 / 2)]) hN'.le
  calc
    _ ≤ 4 * Real.sqrt (x * (1 - x) / N) :=
      hErr.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
    _ ≤ 4 * Real.sqrt ((1 / 4) / N) := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hVar) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1 / 4),
        show Real.sqrt (1 / 4) = 1 / 2 by rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num]
      ring

/-- The weight of the single-edge coefficient squared. -/
noncomputable def edgeWeight (J : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  1 - ∑ j ∈ J, b j ^ 2

/-- The squared coefficient mass through each construction depth. -/
noncomputable def depthWeight (J : Finset ℕ) (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => edgeWeight J b
  | h + 1 => edgeWeight J b + ∑ j ∈ J, b j ^ 2 * (depthWeight J b h) ^ j

/-- The energy estimate forces the single-edge weight to be at least five eighths. -/
theorem edgeWeight_ge {J : Finset ℕ} {b : ℕ → ℝ} (hJ : ∀ j ∈ J, 2 ≤ j)
    (hEnergy : ∑ j ∈ J, (j : ℝ) * b j ^ 2 ≤ 3 / 4) : 5 / 8 ≤ edgeWeight J b := by
  have h := sum_le_sum (s := J) (fun j hj ↦
    mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ j by exact_mod_cast hJ j hj) (sq_nonneg (b j)))
  rw [← mul_sum] at h
  unfold edgeWeight
  linarith

/-- The construction-depth masses stay in the unit interval. -/
theorem depthWeight_mem_interval {J : Finset ℕ} {b : ℕ → ℝ} (hA : 0 ≤ edgeWeight J b) (h : ℕ) :
    depthWeight J b h ∈ Set.Icc 0 1 := by
  induction h with
  | zero =>
    exact ⟨hA, sub_le_self _ (sum_nonneg fun _ _ ↦ sq_nonneg _)⟩
  | succ h ih =>
    rw [depthWeight]
    constructor
    · exact add_nonneg hA (sum_nonneg fun j _ ↦ mul_nonneg (sq_nonneg _) (pow_nonneg ih.1 _))
    · have hBound := sum_le_sum (s := J) (fun j _ ↦
        mul_le_of_le_one_right (sq_nonneg (b j)) (pow_le_one₀ ih.1 ih.2 (n := j)))
      change edgeWeight J b + _ ≤ 1
      unfold edgeWeight
      linarith

/-- The energy bound gives the claimed geometric contraction toward one. -/
theorem one_sub_depthWeight_le {J : Finset ℕ} {b : ℕ → ℝ} (hA : 0 ≤ edgeWeight J b)
    (hEnergy : ∑ j ∈ J, (j : ℝ) * b j ^ 2 ≤ 3 / 4) (h : ℕ) :
    1 - depthWeight J b h ≤ (3 / 4 : ℝ) ^ h * (1 - edgeWeight J b) := by
  induction h with
  | zero => simp [depthWeight]
  | succ h ih =>
    let x := depthWeight J b h
    have hx : x ∈ Set.Icc 0 1 := depthWeight_mem_interval hA h
    have hPow (j : ℕ) : 1 - x ^ j ≤ j * (1 - x) := by
      have hs := abs_pow_sub_pow_le (a := (1 : ℝ)) (b := x) (n := j)
      rw [one_pow, abs_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)),
        abs_of_nonneg (sub_nonneg.mpr hx.2), abs_one, abs_of_nonneg hx.1, max_eq_left hx.2,
        one_pow, mul_one, mul_comm (1 - x)] at hs
      exact hs
    have hID : 1 - depthWeight J b (h + 1) = ∑ j ∈ J, b j ^ 2 * (1 - x ^ j) := by
      rw [depthWeight]
      simp only [edgeWeight, x, mul_sub, sum_sub_distrib, mul_one]
      ring
    calc
      _ = _ := hID
      _ ≤ ∑ j ∈ J, ((j : ℝ) * b j ^ 2) * (1 - x) := sum_le_sum fun j _ ↦ by
        rw [show (j : ℝ) * b j ^ 2 * (1 - x) = b j ^ 2 * (j * (1 - x)) by ring]
        exact mul_le_mul_of_nonneg_left (hPow j) (sq_nonneg _)
      _ ≤ (3 / 4) * (1 - x) := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right hEnergy (sub_nonneg.mpr hx.2)
      _ ≤ (3 / 4 : ℝ) ^ (h + 1) * (1 - edgeWeight J b) := by
        rw [pow_succ', mul_assoc]
        exact mul_le_mul_of_nonneg_left ih (by norm_num)

end LovaszTheta.Independent
