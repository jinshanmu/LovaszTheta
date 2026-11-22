module

public import LovaszTheta.FourierNets
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dyadic chaining for the Fourier kernel process

Apply the increment tail to pairs of nearby net points at consecutive radii.
The entropy and the tail exponent both scale as the inverse square of the
radius. A geometric sum controls the union over the scales.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- Intersection of the Euclidean unit ball and the ℓ¹ ball. -/
def kernelBall (R : ℝ) : Set (ZMod n → ℝ) := {x | (∑ i, x i ^ 2) ≤ 1 ∧ ellOne x ≤ R}

/-- The Fourier kernel process restricted to real vectors. -/
noncomputable def realKernelProcess (signs : InversionClass n → Bool) (x : ZMod n → ℝ) : ℝ :=
  kernelProcess signs (fun i ↦ (x i : ℂ))

lemma realKernelProcess_zero (signs : InversionClass n → Bool) :
    realKernelProcess signs 0 = 0 := by
  unfold realKernelProcess kernelProcess
  have hZero : (fun i : ZMod n ↦ ((0 : ZMod n → ℝ) i : ℂ)) = 0 := by
    ext i
    simp
  rw [hZero]
  simp

private lemma abs_realKernelProcess_sub_le (signs : InversionClass n → Bool)
    {R : ℝ} {x y : ZMod n → ℝ} (hx : x ∈ kernelBall R) (hy : y ∈ kernelBall R)
    {d : ℝ} (hd₀ : 0 ≤ d) (hd : fourierDistance (n := n) x y ≤ d) :
    |realKernelProcess signs x - realKernelProcess signs y| ≤ 2 * d := by
  refine abs_kernelProcess_sub_le signs _ _ ?_ ?_ hd₀ ?_
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hx.1
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hy.1
  · exact (fourierDistance_le_iff _ _ hd₀).mp hd

private lemma probability_realKernelProcess_sub_ge {R : ℝ} {x y : ZMod n → ℝ}
    (hx : x ∈ kernelBall R) (hy : y ∈ kernelBall R) {d t : ℝ} (hd₀ : 0 < d) (ht : 0 < t)
    (hd : fourierDistance (n := n) x y ≤ d) :
    probability (fun signs ↦ t ≤ |realKernelProcess signs x - realKernelProcess signs y|) ≤
      2 * Real.exp (-(t ^ 2) / (16 * d ^ 2 / n)) := by
  refine probability_kernelProcess_sub_ge _ _ ?_ ?_ hd₀ ht ?_
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hx.1
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hy.1
  · exact (fourierDistance_le_iff _ _ hd₀.le).mp hd

/-- The logarithmic scale used in the entropy estimate. -/
noncomputable def kernelLog (n : ℕ) : ℝ := Real.log (8 * n)

/-- Radius of the ℓ¹ ball tested by the kernel process. -/
noncomputable def kernelRadius (n : ℕ) : ℝ :=
  Real.sqrt n / (65536 * kernelLog n ^ 2)

private noncomputable def radius (R : ℝ) (j : ℕ) : ℝ := R / (2 : ℝ) ^ j

private lemma radius_succ (R : ℝ) (j : ℕ) : radius R (j + 1) = radius R j / 2 := by
  simp only [radius, pow_succ, div_div]

private lemma radius_sq (R : ℝ) (j : ℕ) : radius R j ^ 2 = R ^ 2 / (4 : ℝ) ^ j := by
  unfold radius
  rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]
  norm_num

omit [NeZero n] in
lemma kernelLog_one_le (hn : 1 ≤ n) : 1 ≤ kernelLog n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : Real.exp 1 ≤ 8 * n := by linarith [Real.exp_one_lt_three]
  rw [kernelLog, ← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos _) h

private lemma exists_net_at_scale (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    ∃ S : Finset (ZMod n → ℝ), ↑S ⊆ kernelBall (n := n) R ∧
      (S.card : ℝ) ≤ Real.exp (33 * (4 : ℝ) ^ j * kernelLog n ^ 2) ∧
      ∀ x ∈ kernelBall R, ∃ y ∈ S, fourierDistance (n := n) x y ≤ radius R j := by
  let L := kernelLog n
  let q := (4 : ℝ) ^ j
  have hL : 1 ≤ L := kernelLog_one_le hn
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hu : 0 < radius R j := div_pos hR (by positivity)
  let m := ⌈32 * q * L⌉₊
  have hm : 0 < m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hmLower : 32 * q * L ≤ (m : ℝ) := Nat.le_ceil _
  have hExponent : L ≤ (m : ℝ) * radius R j ^ 2 / (32 * R ^ 2) := by
    rw [radius_sq]
    change L ≤ (m : ℝ) * (R ^ 2 / q) / (32 * R ^ 2)
    have hEq : (m : ℝ) * (R ^ 2 / q) / (32 * R ^ 2) = (m : ℝ) / (32 * q) := by
      field_simp
    rw [hEq]
    exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hmLower])
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hn
  have hExp : Real.exp L = (8 * n : ℝ) := Real.exp_log (by positivity)
  have hTail : 4 * n * Real.exp (-(m : ℝ) * radius R j ^ 2 / (32 * R ^ 2)) < 1 := by
    have hLE := Real.exp_le_exp.mpr (show -(m : ℝ) * radius R j ^ 2 / (32 * R ^ 2) ≤ -L by
      rw [neg_mul, neg_div]
      exact neg_le_neg hExponent)
    calc
      _ ≤ 4 * n * Real.exp (-L) := mul_le_mul_of_nonneg_left hLE (by positivity)
      _ = 1 / 2 := by
        rw [Real.exp_neg, hExp]
        field_simp
        norm_num
      _ < _ := by norm_num
  obtain ⟨S, hInside, hCard, hNet⟩ := exists_fourier_net (kernelBall (n := n) R) hR hu
    (fun _ hx ↦ hx.2) hm hTail
  refine ⟨S, hInside, ?_, hNet⟩
  have hmUpper : (m : ℝ) ≤ 33 * q * L := by
    have hRound := Nat.ceil_lt_add_one (show 0 ≤ 32 * q * L by positivity)
    have hqL : 1 ≤ q * L := one_le_mul_of_one_le_of_one_le hq hL
    linarith
  have hN : (2 : ℝ) * n + 1 ≤ 8 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hLog : Real.log (2 * n + 1) ≤ L := Real.log_le_log (by positivity) hN
  calc
    (S.card : ℝ) ≤ (2 * n + 1 : ℝ) ^ m := by exact_mod_cast hCard
    _ = Real.exp ((m : ℝ) * Real.log (2 * n + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ Real.exp ((m : ℝ) * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLog (by positivity))
    _ ≤ Real.exp (33 * q * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (33 * q * L) * L := mul_le_mul_of_nonneg_right hmUpper hLpos.le
        _ = _ := by ring

private lemma exists_dyadic_nets (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) :
    ∃ S : ℕ → Finset (ZMod n → ℝ), S 0 = {0} ∧
      (∀ j, ↑(S j) ⊆ kernelBall (n := n) R) ∧
      (∀ j, ((S j).card : ℝ) ≤ Real.exp (33 * (4 : ℝ) ^ j * kernelLog n ^ 2)) ∧
      ∀ j, ∀ x ∈ kernelBall R, ∃ y ∈ S j, fourierDistance (n := n) x y ≤ radius R j := by
  choose T hT hCard hNet using fun j ↦ exists_net_at_scale hn hR j
  let S : ℕ → Finset (ZMod n → ℝ) := fun j ↦ if j = 0 then {0} else T j
  have hZeroBall : (0 : ZMod n → ℝ) ∈ kernelBall R := by
    constructor
    · simp
    · simpa [ellOne] using hR.le
  refine ⟨S, by simp [S], ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · simp [S, hj, hZeroBall]
    · simpa [S, hj] using hT j
  · intro j
    by_cases hj : j = 0
    · simpa [S, hj] using Real.one_le_exp (by positivity : 0 ≤ 33 * kernelLog n ^ 2)
    · simpa [S, hj] using hCard j
  · intro j x hx
    by_cases hj : j = 0
    · refine ⟨0, by simp [S, hj], ?_⟩
      simpa [hj, radius] using (fourierDistance_zero_le x).trans hx.2
    · simpa [S, hj] using hNet j x hx

private lemma probability_bad_pair {R d t : ℝ} (hd : 0 < d) (ht : 0 < t)
    (S T : Finset (ZMod n → ℝ)) (hS : ↑S ⊆ kernelBall (n := n) R) (hT : ↑T ⊆ kernelBall (n := n) R) :
    probability (fun signs : InversionClass n → Bool ↦ ∃ x : S, ∃ y : T, fourierDistance (n := n) x y ≤ d ∧
      t ≤ |realKernelProcess signs x - realKernelProcess signs y|) ≤
      (S.card : ℝ) * T.card * (2 * Real.exp (-(t ^ 2) / (16 * d ^ 2 / n))) := by
  let e := 2 * Real.exp (-(t ^ 2) / (16 * d ^ 2 / n))
  have hOne (x : S) (y : T) :
      probability (fun signs : InversionClass n → Bool ↦ fourierDistance (n := n) x y ≤ d ∧
        t ≤ |realKernelProcess signs x - realKernelProcess signs y|) ≤ e := by
    by_cases hxy : fourierDistance (n := n) x y ≤ d
    · exact (probability_mono fun _ h ↦ h.2).trans
        (probability_realKernelProcess_sub_ge (hS x.property) (hT y.property) hd ht hxy)
    · have hP : probability (fun signs : InversionClass n → Bool ↦ fourierDistance (n := n) x y ≤ d ∧
          t ≤ |realKernelProcess signs x - realKernelProcess signs y|) = 0 := by
        simp [probability, hxy, average]
      rw [hP]
      dsimp [e]
      positivity
  calc
    _ ≤ ∑ x : S, probability (fun signs : InversionClass n → Bool ↦ ∃ y : T, fourierDistance (n := n) x y ≤ d ∧
        t ≤ |realKernelProcess signs x - realKernelProcess signs y|) := probability_exists_le_sum _
    _ ≤ ∑ x : S, ∑ y : T, probability (fun signs : InversionClass n → Bool ↦ fourierDistance (n := n) x y ≤ d ∧
        t ≤ |realKernelProcess signs x - realKernelProcess signs y|) :=
      sum_le_sum fun _ _ ↦ probability_exists_le_sum _
    _ ≤ ∑ _x : S, ∑ _y : T, e :=
      sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ hOne x y
    _ = _ := by simp [nsmul_eq_mul, mul_assoc, e]

private lemma probability_bad_scale (R : ℝ) (hR : 0 < R)
    (S : ℕ → Finset (ZMod n → ℝ)) (hInside : ∀ j, ↑(S j) ⊆ kernelBall (n := n) R)
    (hCard : ∀ j, ((S j).card : ℝ) ≤ Real.exp (33 * (4 : ℝ) ^ j * kernelLog n ^ 2))
    (hn : 1 ≤ n) (j : ℕ) :
    probability (fun signs : InversionClass n → Bool ↦ ∃ x : S j, ∃ y : S (j+1), fourierDistance (n := n) x y ≤ 3 * radius R j ∧
      300 * R * kernelLog n / Real.sqrt n ≤
        |realKernelProcess signs x - realKernelProcess signs y|) ≤
      2 * Real.exp (-((4 : ℝ) ^ j * kernelLog n ^ 2)) := by
  let L := kernelLog n
  let u := radius R j
  let t := 300 * R * L / Real.sqrt n
  let q := (4 : ℝ) ^ j
  have hL : 0 < L := zero_lt_one.trans_le (kernelLog_one_le hn)
  have hu : 0 < u := div_pos hR (by positivity)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have ht : 0 < t := by dsimp [t]; positivity
  have hExp : -(t ^ 2) / (16 * (3 * u) ^ 2 / n) = -(625 * q * L ^ 2) := by
    dsimp only [t, u, q]
    rw [div_pow, Real.sq_sqrt hnR.le, mul_pow (3 : ℝ), radius_sq]
    field_simp
    ring
  have hBound := probability_bad_pair (R := R) (d := 3 * u) (t := t)
    (by positivity) ht (S j) (S (j + 1)) (hInside j) (hInside (j + 1))
  change _ ≤ 2 * Real.exp (-(q * L ^ 2))
  apply hBound.trans
  rw [hExp]
  have hCard₁ : ((S j).card : ℝ) ≤ Real.exp (33 * q * L ^ 2) := hCard j
  have hCard₂ : ((S (j + 1)).card : ℝ) ≤ Real.exp (132 * q * L ^ 2) := by
    convert hCard (j + 1) using 3
    dsimp [q]
    rw [pow_succ]
    ring
  calc
    _ ≤ (Real.exp (33 * q * L ^ 2) * Real.exp (132 * q * L ^ 2)) *
        (2 * Real.exp (-(625 * q * L ^ 2))) := by gcongr
    _ = 2 * Real.exp (-(460 * q * L ^ 2)) := by
      rw [← Real.exp_add]
      rw [show Real.exp (33 * q * L ^ 2 + 132 * q * L ^ 2) *
          (2 * Real.exp (-(625 * q * L ^ 2))) =
        2 * (Real.exp (33 * q * L ^ 2 + 132 * q * L ^ 2) *
          Real.exp (-(625 * q * L ^ 2))) by ring]
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      nlinarith only [show 0 ≤ q * L ^ 2 by positivity]

private lemma sum_dyadic_tails_le (J : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    (∑ j ∈ range J, 2 * Real.exp (-((4 : ℝ) ^ j * L ^ 2))) ≤ 4 * Real.exp (-(L ^ 2)) := by
  have hPow (j : ℕ) : (j : ℝ) + 1 ≤ (4 : ℝ) ^ j := by
    induction j with
    | zero => norm_num
    | succ j hj =>
      have := mul_le_mul_of_nonneg_right hj (show (0 : ℝ) ≤ 4 by norm_num)
      rw [Nat.cast_succ, pow_succ]
      linarith only [this, Nat.cast_nonneg (α := ℝ) j]
  let a := Real.exp (-(L ^ 2))
  have ha : 0 < a := Real.exp_pos _
  have hAhalf : a < 1 / 2 := by
    have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have he : a ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have ht : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, ← one_div (Real.exp 1)]
      exact one_div_lt_one_div_of_lt (by norm_num) Real.exp_one_gt_two
    exact he.trans_lt ht
  have hGeom : (∑ j ∈ range J, a ^ j) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) ha.le (show a < 1 by linarith)
    rw [Nat.Ico_zero_eq_range, pow_zero] at h
    exact h.trans ((div_le_iff₀ (by linarith : 0 < 1 - a)).mpr (by linarith))
  calc
    _ ≤ ∑ j ∈ range J, 2 * (a * a ^ j) := sum_le_sum fun j _ ↦ by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have he : -((4 : ℝ) ^ j * L ^ 2) ≤ -(((j : ℝ) + 1) * L ^ 2) :=
        neg_le_neg (mul_le_mul_of_nonneg_right (hPow j) (sq_nonneg L))
      apply (Real.exp_le_exp.mpr he).trans_eq
      dsimp [a]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ = 2 * a * ∑ j ∈ range J, a ^ j := by simp_rw [mul_assoc, ← mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hGeom (show 0 ≤ 2 * a by positivity)
      change _ ≤ 4 * a
      linarith

private lemma chain_to_ball {R t : ℝ} (hR : 0 < R)
    (S : ℕ → Finset (ZMod n → ℝ)) (hZero : S 0 = {0})
    (hInside : ∀ j, ↑(S j) ⊆ kernelBall (n := n) R)
    (hNet : ∀ j, ∀ x ∈ kernelBall R, ∃ y ∈ S j, fourierDistance (n := n) x y ≤ radius R j)
    (J : ℕ) (signs : InversionClass n → Bool)
    (hGood : ¬∃ j : Fin J, ∃ x : S j.val, ∃ y : S (j.val+1),
      fourierDistance (n := n) x y ≤ 3 * radius R j.val ∧
        t ≤ |realKernelProcess signs x - realKernelProcess signs y|)
    {x : ZMod n → ℝ} (hx : x ∈ kernelBall R) :
    |realKernelProcess signs x| ≤ (J : ℝ) * t + 2 * radius R J := by
  choose y hY hDist using fun j ↦ hNet j x hx
  have hYZero : y 0 = 0 := by simpa [hZero] using hY 0
  have hAccum (j : ℕ) (hj : j ≤ J) :
      |realKernelProcess signs (y j)| ≤ (j : ℝ) * t := by
    induction j with
    | zero => simp [hYZero, realKernelProcess_zero]
    | succ j ih =>
      have hj' : j < J := hj
      have hPrev := ih hj'.le
      have hu : 0 ≤ radius R j := div_nonneg hR.le (by positivity)
      have hPair : fourierDistance (y j) (y (j + 1)) ≤ 3 * radius R j := by
        have h := fourierDistance_triangle (y j) x (y (j + 1))
        rw [fourierDistance_comm (y j) x] at h
        have hb := add_le_add (hDist j) (hDist (j + 1))
        rw [radius_succ] at hb
        linarith
      have hInc : |realKernelProcess signs (y (j + 1)) - realKernelProcess signs (y j)| ≤ t := by
        have hn : ¬ t ≤ |realKernelProcess signs (y j) - realKernelProcess signs (y (j+1))| :=
          fun he ↦ hGood ⟨⟨j, hj'⟩, ⟨y j, hY j⟩, ⟨y (j+1), hY (j+1)⟩, hPair, he⟩
        rw [abs_sub_comm]
        exact (lt_of_not_ge hn).le
      calc
        _ ≤ |realKernelProcess signs (y (j + 1)) - realKernelProcess signs (y j)| +
            |realKernelProcess signs (y j)| := by
          simpa only [sub_add_cancel] using abs_add_le
            (realKernelProcess signs (y (j + 1)) - realKernelProcess signs (y j))
            (realKernelProcess signs (y j))
        _ ≤ t + (j : ℝ) * t := add_le_add hInc hPrev
        _ = _ := by push_cast; ring
  have hLast := abs_realKernelProcess_sub_le signs hx (hInside J (hY J))
    (show 0 ≤ radius R J from div_nonneg hR.le (by positivity)) (hDist J)
  calc
    _ ≤ |realKernelProcess signs x - realKernelProcess signs (y J)| +
        |realKernelProcess signs (y J)| := by
      simpa only [sub_add_cancel] using abs_add_le
        (realKernelProcess signs x - realKernelProcess signs (y J)) (realKernelProcess signs (y J))
    _ ≤ _ := by linarith [hAccum J le_rfl]

/-- The intersection of balls has uniformly small quadratic process with
failure probability exponentially small in the square of the logarithm. -/
theorem probability_kernelBall_large (hn : 1 ≤ n) :
    probability (fun signs ↦ ∃ x ∈ kernelBall (n := n) (kernelRadius n),
      (1 / 2 : ℝ) < |realKernelProcess signs x|) ≤
      4 * Real.exp (-(kernelLog n ^ 2)) := by
  let L := kernelLog n
  let R := kernelRadius n
  let J := ⌈2 * L⌉₊
  let t := 300 * R * L / Real.sqrt n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hL : 1 ≤ L := kernelLog_one_le hn
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hR : 0 < R := by dsimp only [R, kernelRadius]; positivity
  obtain ⟨S, hS0, hInside, hCard, hNet⟩ := exists_dyadic_nets (n := n) hn hR
  let bad (signs : InversionClass n → Bool) (j : Fin J) :=
    ∃ x : S j.val, ∃ y : S (j.val+1),
      fourierDistance (n := n) x y ≤ 3 * radius R j.val ∧
        t ≤ |realKernelProcess signs x - realKernelProcess signs y|
  have hJUpper : (J : ℝ) ≤ 3 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * L by positivity)
    dsimp only [J]
    linarith
  have hJL : 2 * L ≤ (J : ℝ) := Nat.le_ceil _
  have hLogTwo : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJpow : (8 * n : ℝ) ≤ 2 ^ J := by
    rw [← Real.exp_log (show 0 < (8 * n : ℝ) by positivity), ← Real.exp_log (by norm_num : 0 < (2:ℝ)),
      ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change L ≤ (J : ℝ) * Real.log 2
    have := mul_le_mul_of_nonneg_left hLogTwo (Nat.cast_nonneg (α := ℝ) J)
    linarith
  have hRsmall : 32 * R ≤ (8 * n : ℝ) := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have hSqrt : Real.sqrt (n : ℝ) ≤ n := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (by positivity : 0 ≤ (n:ℝ))]⟩
    have hEq : R = Real.sqrt (n : ℝ) / (65536 * L ^ 2) := rfl
    rw [hEq, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hSqrt, mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ (n:ℝ))]
  have hLast : radius R J ≤ 1 / 32 := by
    unfold radius
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hRsmall.trans hJpow]
  have hTotal : (J : ℝ) * t + 2 * radius R J ≤ 1 / 2 := by
    have ht : t = 300 / (65536 * L) := by
      change 300 * (Real.sqrt (n : ℝ) / (65536 * L ^ 2)) * L / Real.sqrt (n : ℝ) = _
      field_simp
    rw [ht]
    have h := mul_le_mul_of_nonneg_right hJUpper
      (show 0 ≤ (300 : ℝ) / (65536 * L) by positivity)
    have hCancel : 3 * L * (300 / (65536 * L)) = (900 : ℝ) / 65536 := by
      field_simp
      norm_num
    rw [hCancel] at h
    linarith
  have hImp (signs : InversionClass n → Bool)
      (h : ∃ x ∈ kernelBall R, (1 / 2 : ℝ) < |realKernelProcess signs x|) :
      ∃ j, bad signs j := by
    by_contra hFail
    obtain ⟨x, hx, hToo⟩ := h
    have hX := chain_to_ball hR S hS0 hInside hNet J signs hFail hx
    exact (not_lt_of_ge (hX.trans hTotal)) hToo
  calc
    _ ≤ probability (fun signs ↦ ∃ j, bad signs j) := probability_mono hImp
    _ ≤ ∑ j : Fin J, probability (fun signs ↦ bad signs j) := probability_exists_le_sum _
    _ ≤ ∑ j : Fin J, 2 * Real.exp (-((4 : ℝ) ^ j.val * L ^ 2)) :=
      sum_le_sum fun j _ ↦ probability_bad_scale R hR S hInside hCard hn j.val
    _ ≤ _ := by
      simpa only [Fin.sum_univ_eq_sum_range (fun j ↦ 2 * Real.exp (-((4 : ℝ) ^ j * L ^ 2)))]
        using sum_dyadic_tails_le J hL

end LovaszTheta.Circulant
