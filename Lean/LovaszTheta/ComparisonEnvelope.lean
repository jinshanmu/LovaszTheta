module

public import LovaszTheta.GaussianComparison

/-!
# Uniform envelope for the Gaussian comparison

The moment factors of the interpolation proof are bounded by the
manuscript's exponential envelope in tree size and test degree.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace LovaszTheta.Circulant

private lemma self_le_exp (x : ℝ) : x ≤ Real.exp x :=
  (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)

private lemma mul_le_exp_add {x y u v : ℝ} (hx : x ≤ Real.exp u) (hy : y ≤ Real.exp v) (hy0 : 0 ≤ y) :
    x*y ≤ Real.exp (u+v) := by
  rw [Real.exp_add]
  exact mul_le_mul hx hy hy0 (Real.exp_nonneg _)

private lemma pow_le_exp_mul {x u : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp u) (j : ℕ) :
    x^j ≤ Real.exp ((j : ℝ)*u) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hx0 hx _

private lemma sqrt_le_exp_of_le_exp {x u : ℝ} (hu : 0 ≤ u) (hx : x ≤ Real.exp u) :
    Real.sqrt x ≤ Real.exp u := by
  apply (Real.sqrt_le_left (Real.exp_nonneg _)).mpr
  exact hx.trans (by rw [pow_two]; exact le_mul_of_one_le_right (Real.exp_nonneg _) (Real.one_le_exp hu))

lemma treeMomentEnvelope_le_exp (D : ℕ) :
    treeMomentEnvelope D ≤ Real.exp (28*(D : ℝ)^2) := by
  unfold treeMomentEnvelope
  refine (pow_le_exp_mul (by positivity) (self_le_exp (2*(D : ℝ))) _).trans_eq ?_
  push_cast
  congr 1
  ring

private lemma bounded_sum_le_exp {x y u : ℝ} (hx : x ≤ Real.exp u) (hy : y ≤ Real.exp u) :
    x+y ≤ Real.exp (2+u) := by
  rw [Real.exp_add]
  calc
    _ ≤ 2 * Real.exp u := by linarith only [hx, hy]
    _ ≤ _ := mul_le_mul_of_nonneg_right (self_le_exp 2) (Real.exp_nonneg _)

lemma comparisonSignGrowth_le_exp (D r : ℕ) (A u : ℝ) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hAu : A ≤ Real.exp u) :
    comparisonSignGrowth D r A ≤ Real.exp
      (6*(r : ℝ)+3+(r : ℝ)*(2*r*D+2*u+28*(D : ℝ)^2)) := by
  let s := (r : ℝ)*(2*r*D+2*u+28*(D : ℝ)^2)
  let q := ((2*r-1 : ℕ) : ℝ)
  let L := (q^D*A^2*treeMomentEnvelope D)^r
  have hQ0 : 0 ≤ q := by unfold q; positivity
  have hQ : q ≤ Real.exp (2*r) := by
    have h : q ≤ 2*(r : ℝ) := by
      unfold q
      exact_mod_cast Nat.sub_le (2*r) 1
    exact h.trans (self_le_exp _)
  have hA2 : A^2 ≤ Real.exp (2*u) := pow_le_exp_mul hA hAu 2
  have hB0 : 0 ≤ treeMomentEnvelope D := by unfold treeMomentEnvelope; positivity
  have hBase : q^D*A^2*treeMomentEnvelope D ≤ Real.exp (2*r*D+2*u+28*(D : ℝ)^2) := by
    have hq := pow_le_exp_mul hQ0 hQ D
    rw [show (D : ℝ)*(2*r) = 2*r*D by ring] at hq
    exact mul_le_exp_add (mul_le_exp_add hq hA2 (sq_nonneg _)) (treeMomentEnvelope_le_exp D) hB0
  have hL : L ≤ Real.exp s := pow_le_exp_mul (by positivity) hBase r
  have hs : 0 ≤ s := by unfold s; positivity
  have hSum : 1+L+L ≤ Real.exp (3+s) := by
    rw [Real.exp_add]
    have h := Real.one_le_exp hs
    exact (show 1+L+L ≤ 3*Real.exp s by linarith only [hL, h]).trans
      (mul_le_mul_of_nonneg_right (self_le_exp 3) (Real.exp_nonneg _))
  have h₃ : (3 : ℝ)^(2*r) ≤ Real.exp (6*(r : ℝ)) := by
    have h := pow_le_exp_mul (by norm_num : 0 ≤ (3 : ℝ)) (self_le_exp 3) (2*r)
    convert h using 2
    push_cast
    ring
  change Real.sqrt ((3 : ℝ)^(2*r)*(1+L+L)) ≤ _
  have h := sqrt_le_exp_of_le_exp (show 0 ≤ 6*(r : ℝ)+(3+s) by positivity)
    (mul_le_exp_add h₃ hSum (by unfold L; positivity))
  simpa only [add_assoc, s] using h

private lemma comparisonGaussianGrowth_le_exp (r : ℕ) (v : ℝ≥0) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hv : (v : ℝ) ≤ C₀) :
    comparisonGaussianGrowth v r ≤ Real.exp (3*(r : ℝ)+3+2*(r : ℝ)^2*C₀) := by
  let u := 2*(r : ℝ)^2*C₀
  have hu : 0 ≤ u := by unfold u; positivity
  have h₁ : ((2*r : ℝ)*(v : ℝ))^r ≤ Real.exp u := by
    have hBase : (2*r : ℝ)*(v : ℝ) ≤ Real.exp (2*r*C₀) :=
      (mul_le_mul_of_nonneg_left hv (by positivity)).trans (self_le_exp _)
    exact (pow_le_exp_mul (by positivity) hBase _).trans_eq (by unfold u; congr 1; ring)
  have hSum : 2+((2*r : ℝ)*(v : ℝ))^r ≤ Real.exp (3+u) := by
    rw [Real.exp_add]
    exact (show _ ≤ 3*Real.exp u by linarith only [Real.one_le_exp hu, h₁]).trans
      (mul_le_mul_of_nonneg_right (self_le_exp 3) (Real.exp_nonneg _))
  have h₃ : (3 : ℝ)^r ≤ Real.exp (3*(r : ℝ)) := by
    rw [mul_comm]
    exact pow_le_exp_mul (by norm_num) (self_le_exp 3) _
  unfold comparisonGaussianGrowth
  simpa only [add_assoc] using mul_le_exp_add h₃ hSum (by positivity)

private lemma comparison_pairing_factors_le_exp (D : ℕ) (A u : ℝ)
    (hA : 0 ≤ A) (hu : 0 ≤ u) (hAu : A ≤ Real.exp u) :
    let B := treeMomentEnvelope D
    A^2*(Real.sqrt B+B) +
      (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt B)*(A^2*((D : ℝ)*B))) ≤
        Real.exp (4+16*(D : ℝ)+3*u+56*(D : ℝ)^2) := by
  let B := treeMomentEnvelope D
  let p := 28*(D : ℝ)^2
  have hB0 : 0 ≤ B := by unfold B treeMomentEnvelope; positivity
  have hB : B ≤ Real.exp p := treeMomentEnvelope_le_exp D
  have hBs : Real.sqrt B ≤ Real.exp p := sqrt_le_exp_of_le_exp (by unfold p; positivity) hB
  have hA2 : A^2 ≤ Real.exp (2*u) := pow_le_exp_mul hA hAu 2
  have hL : A^2*(Real.sqrt B+B) ≤ Real.exp (2*u+(2+p)) :=
    mul_le_exp_add hA2 (bounded_sum_le_exp hBs hB) (by positivity)
  have hH : (Real.sqrt ((5 : ℝ)^D))^3 ≤ Real.exp (15*(D : ℝ)) := by
    have hf := pow_le_exp_mul (by norm_num : 0 ≤ (5 : ℝ)) (self_le_exp 5) D
    have hs := sqrt_le_exp_of_le_exp (by positivity : 0 ≤ (D : ℝ)*5) hf
    exact (pow_le_exp_mul (Real.sqrt_nonneg _) hs 3).trans_eq (by push_cast; congr 1; ring)
  have hD : (D : ℝ) ≤ Real.exp D := self_le_exp _
  have hR : (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt B)*(A^2*((D : ℝ)*B))) ≤
      Real.exp (15*(D : ℝ)+((u+p)+(2*u+(D+p)))) :=
    mul_le_exp_add hH (mul_le_exp_add (mul_le_exp_add hAu hBs (Real.sqrt_nonneg _))
      (mul_le_exp_add hA2 (mul_le_exp_add hD hB hB0) (by positivity)) (by positivity)) (by positivity)
  let v := 2+16*(D : ℝ)+3*u+56*(D : ℝ)^2
  have h₁ : 2*u+(2+p) ≤ v := by unfold v p; nlinarith only [hu, sq_nonneg (D : ℝ), Nat.cast_nonneg (α := ℝ) D]
  have h₂ : 15*(D : ℝ)+((u+p)+(2*u+(D+p))) ≤ v := by unfold v p; linarith
  exact (bounded_sum_le_exp (hL.trans (Real.exp_le_exp.mpr h₁)) (hR.trans (Real.exp_le_exp.mpr h₂))).trans_eq
    (by unfold v; congr 1; ring)

private lemma comparison_factors_le_exp (D r : ℕ) (A C₀ : ℝ) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀)
    (hAC : A ≤ C₀*4^D) (v : ℝ≥0) (hv : (v : ℝ) ≤ C₀) :
    let B := treeMomentEnvelope D
    comparisonSignGrowth D r A * comparisonGaussianGrowth v r *
      (A^2*(Real.sqrt B+B) +
        (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt B)*(A^2*((D : ℝ)*B)))) ≤
          Real.exp (200*(C₀+1)*(((D : ℝ)+1)*((r : ℝ)+1))^2) := by
  let u := C₀+4*(D : ℝ)
  have hu : 0 ≤ u := by unfold u; positivity
  have h4 : (4 : ℝ)^D ≤ Real.exp (4*(D : ℝ)) := by
    rw [mul_comm]
    exact pow_le_exp_mul (by norm_num) (self_le_exp 4) _
  have hAu : A ≤ Real.exp u := hAC.trans (mul_le_exp_add (self_le_exp C₀) h4 (by positivity))
  have h := mul_le_exp_add
    (mul_le_exp_add (comparisonSignGrowth_le_exp D r A u hA hu hAu)
      (comparisonGaussianGrowth_le_exp r v C₀ hC₀ hv) (by unfold comparisonGaussianGrowth; positivity))
    (comparison_pairing_factors_le_exp D A u hA hu hAu) (by
      unfold treeMomentEnvelope
      positivity)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  let p := (((D : ℝ)+1)*((r : ℝ)+1))^2
  have hp (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) : (D : ℝ)^i*(r : ℝ)^j ≤ p := by
    have hd : (D : ℝ)^i ≤ ((D : ℝ)+1)^2 :=
      (pow_le_pow_left₀ (by positivity) (by linarith : (D : ℝ) ≤ (D : ℝ)+1) _).trans
        (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) D]) hi)
    have hr : (r : ℝ)^j ≤ ((r : ℝ)+1)^2 :=
      (pow_le_pow_left₀ (by positivity) (by linarith : (r : ℝ) ≤ (r : ℝ)+1) _).trans
        (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) r]) hj)
    exact (mul_le_mul hd hr (by positivity) (by positivity)).trans_eq (by unfold p; rw [mul_pow])
  have hp₀ : (1 : ℝ) ≤ p := by simpa only [pow_zero, mul_one] using hp 0 0 (by decide) (by decide)
  have hpD : (D : ℝ) ≤ p := by simpa only [pow_one, pow_zero, mul_one] using hp 1 0 (by decide) (by decide)
  have hpD2 : (D : ℝ)^2 ≤ p := by simpa only [pow_zero, mul_one] using hp 2 0 (by decide) (by decide)
  have hpr : (r : ℝ) ≤ p := by simpa only [pow_one, pow_zero, one_mul] using hp 0 1 (by decide) (by decide)
  have hpr2 : (r : ℝ)^2 ≤ p := by simpa only [pow_zero, one_mul] using hp 0 2 (by decide) (by decide)
  have hpDr : (D : ℝ)*(r : ℝ) ≤ p := by simpa only [pow_one] using hp 1 1 (by decide) (by decide)
  have hpDr2 : (D : ℝ)*(r : ℝ)^2 ≤ p := by simpa only [pow_one] using hp 1 2 (by decide) (by decide)
  have hpD2r : (D : ℝ)^2*(r : ℝ) ≤ p := by simpa only [pow_one] using hp 2 1 (by decide) (by decide)
  change _ ≤ 200*(C₀+1)*p
  unfold u
  nlinarith only [hp₀, hpD, hpD2, hpr, hpDr, hpDr2, hpD2r,
    mul_le_mul_of_nonneg_left hp₀ hC₀, mul_le_mul_of_nonneg_left hpr hC₀,
    mul_le_mul_of_nonneg_left hpr2 hC₀]

/-- An explicit choice of the comparison envelope for tests with
growth exponent `2*M+3`. -/
noncomputable def comparisonEnvelope (C₀ : ℝ) (D M : ℕ) : ℝ :=
  Real.exp (3200*(C₀+1)*(((D : ℝ)+1)*((M : ℝ)+1))^2)

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n] [Nonempty (InversionClass n)]

/-- Smooth test functions obey the regular-frequency Gaussian comparison
with the explicit exponential envelope and inverse-square-root rate. -/
theorem abs_average_treeTest_sub_le_envelope (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    (D M : ℕ) (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (hAC : (∑ i, |a i|) ≤ C₀*4^D)
    (v : ℝ≥0) (hv : (v : ℝ) = ∑ i, a i^2) (hVC : (v : ℝ) ≤ C₀)
    (C : ℝ) (hC : 0 ≤ C) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (hGrow : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j ψ x| ≤ C*(1+|x|)^(2*M+3)) :
    |average (fun x ↦ ψ (linearWalsh a (treeCoefficients T k) x)) -
      ∫ g, ψ g ∂gaussianReal 0 v| ≤ C*comparisonEnvelope C₀ D M / Real.sqrt n := by
  let A := ∑ i, |a i|
  let B := treeMomentEnvelope D
  let r := 2*M+3
  have hB : 0 ≤ B := by unfold B treeMomentEnvelope; positivity
  have hA : 0 ≤ A := by unfold A; positivity
  have hn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  have hBase := abs_average_treeTest_sub_gaussian_le (r := r) a T k (by unfold r; omega)
    hD hk hDistinct v hv C hC ψ hψ hGrow
  have hP : (((D : ℝ)+1)*((r : ℝ)+1))^2 ≤ 16*(((D : ℝ)+1)*((M : ℝ)+1))^2 := by
    have hr : (r : ℝ)+1 ≤ 4*((M : ℝ)+1) := by unfold r; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M]
    calc
      _ ≤ (((D : ℝ)+1)*(4*((M : ℝ)+1)))^2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hr (by positivity)) _
      _ = _ := by ring
  have hEnv := comparison_factors_le_exp D r A C₀ hA hC₀ hAC v hVC
  have hExp : Real.exp (200*(C₀+1)*(((D : ℝ)+1)*((r : ℝ)+1))^2) ≤
      comparisonEnvelope C₀ D M := by
    unfold comparisonEnvelope
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 200*(C₀+1))).trans_eq (by ring))
  refine hBase.trans ?_
  change (C/2) * comparisonSignGrowth D r A * comparisonGaussianGrowth v r *
    (A^2*(Real.sqrt (B/n)+B/Real.sqrt n) +
      (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt (B/n))*(A^2*((D : ℝ)*B)))) ≤ _
  rw [Real.sqrt_div hB]
  let Q := comparisonSignGrowth D r A * comparisonGaussianGrowth v r *
    (A^2*(Real.sqrt B+B) + (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt B)*(A^2*((D : ℝ)*B))))
  have hQ : 0 ≤ Q := by unfold Q comparisonSignGrowth comparisonGaussianGrowth; positivity
  calc
    _ = (C/2)*Q / Real.sqrt n := by unfold Q; ring
    _ ≤ C*Q / Real.sqrt n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hQ) hn.le
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hEnv.trans hExp) hC) hn.le

end LovaszTheta.Circulant
