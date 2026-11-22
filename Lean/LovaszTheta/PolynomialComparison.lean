module

public import LovaszTheta.PolarizedMoments
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial tests for the tree fields

Each monomial is treated by its signed polarization. At arbitrary
frequencies the absolute moment is bounded by the even moments
of its factors. Summation costs the absolute coefficient sum.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I]

private lemma exists_monomial_positions (m : I →₀ ℕ) :
    ∃ u : Fin (∑ i, m i) → I, ∀ x : I → ℝ, (∏ p, x (u p)) = ∏ i, x i^(m i) := by
  have hc : Fintype.card (Fin (∑ i, m i)) = Fintype.card (Σ i : I, Fin (m i)) := by
    simp [Fintype.card_sigma]
  let e := Fintype.equivOfCardEq hc
  refine ⟨fun p ↦ (e p).1, fun x ↦ ?_⟩
  rw [Equiv.prod_comp e (fun p ↦ x p.1), Fintype.prod_sigma]
  simp

private lemma monomial_degree_le (p : MvPolynomial I ℝ) {m : I →₀ ℕ} (hm : m ∈ p.support) :
    (∑ i, m i) ≤ p.totalDegree := by
  simpa only [Finsupp.sum_fintype m (fun _ e ↦ e) (fun _ ↦ rfl)] using MvPolynomial.le_totalDegree hm

private lemma integrable_gaussianCoordinates_pow_product (m : I →₀ ℕ) :
    Integrable (fun x : I → ℝ ↦ ∏ i, x i^(m i)) (gaussianCoordinates I) := by
  obtain ⟨u, hu⟩ := exists_monomial_positions m
  simp_rw [← hu]
  exact integrable_gaussianCoordinates_monomial u

private lemma average_finsetSum {Ω J : Type*} [Fintype Ω] (s : Finset J) (f : J → Ω → ℝ) :
    average (fun x ↦ ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  unfold average
  rw [sum_comm, sum_div]

/-- The absolute coefficient sum in the power basis. -/
noncomputable def absCoefficientSum (p : MvPolynomial I ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

variable {n : ℕ} [NeZero n]

/-- At regular frequencies polynomial expectations agree with the Gaussian
expectation to the comparison error times the coefficient sum. -/
theorem abs_average_treePolynomial_sub_gaussian_le [Nonempty (InversionClass n)] (T : I → RootedTree)
    (k : I → ZMod n) (D M : ℕ) (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j)
    (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ 2*M) :
    |average (fun x ↦ p.eval (fun i ↦ (T i).field x (k i))) -
      (∫ x, p.eval x ∂gaussianCoordinates I)| ≤ absCoefficientSum p *
        (comparisonEnvelope 2 D M / Real.sqrt n) := by
  have hi (m : I →₀ ℕ) := (integrable_gaussianCoordinates_pow_product m).const_mul (p.coeff m)
  simp_rw [MvPolynomial.eval_eq', average_finsetSum, average_mul_left]
  rw [integral_finsetSum _ fun m _ ↦ hi m]
  simp_rw [integral_const_mul, ← sum_sub_distrib, ← mul_sub]
  unfold absCoefficientSum
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm ↦ ?_)
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  obtain ⟨u, hu⟩ := exists_monomial_positions m
  simp_rw [← hu]
  exact abs_average_treeMonomial_sub_gaussian_le T k D M hD hk hDistinct ((monomial_degree_le p hm).trans hp) u

private lemma abs_pow_le_one_add_even_pow (y : ℝ) {d M : ℕ} (hd : d ≤ 2*M) :
    |y|^d ≤ 1+y^(2*M) := by
  rw [← abs_pow_even]
  by_cases h : |y|≤1
  · exact (pow_le_one₀ (abs_nonneg _) h).trans (le_add_of_nonneg_right (by positivity))
  · exact (pow_le_pow_right₀ (le_of_not_ge h) hd).trans (le_add_of_nonneg_left zero_le_one)

private lemma product_abs_le_average_pow {d : ℕ} (hd : 0 < d) (y : Fin d → ℝ) :
    (∏ j, |y j|) ≤ average (fun j ↦ |y j|^d) := by
  let w : ℝ := (d : ℝ)⁻¹
  have hR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw : (∑ _ : Fin d, w) = 1 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, w, mul_inv_cancel₀ hR]
  have h := Real.geom_mean_le_arith_mean_weighted univ (fun _ : Fin d ↦ w)
    (fun j ↦ |y j|^d) (fun _ _ ↦ by unfold w; positivity) hw (fun _ _ ↦ by positivity)
  have he (j : Fin d) : (|y j|^d)^w = |y j| := by
    rw [← Real.rpow_natCast_mul (abs_nonneg _), show (d : ℝ)*w = 1 from mul_inv_cancel₀ hR, Real.rpow_one]
  simp_rw [he, ← mul_sum] at h
  simpa only [average, Fintype.card_fin, div_eq_inv_mul, w] using h

private lemma moment_bound_le_comparisonEnvelope (D M : ℕ) :
    1+((((2*M-1 : ℕ) : ℝ)^D)*treeMomentEnvelope D)^M ≤ comparisonEnvelope 2 D M := by
  let q := ((2*M-1 : ℕ) : ℝ)
  let z := (M : ℝ)*(2*M*D+28*(D : ℝ)^2)
  have hq : q ≤ Real.exp (2*M) := by
    have h : q ≤ 2*(M : ℝ) := by unfold q; exact_mod_cast Nat.sub_le (2*M) 1
    exact h.trans (by linarith only [Real.add_one_le_exp (2 * (M : ℝ))])
  have hqD : q^D ≤ Real.exp (2*M*D) := by
    rw [show 2*(M : ℝ)*D = (D : ℝ)*(2*M) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by unfold q; positivity) hq _
  have hB : 0 ≤ treeMomentEnvelope D := by unfold treeMomentEnvelope; positivity
  have hBase : q^D*treeMomentEnvelope D ≤ Real.exp (2*M*D+28*(D : ℝ)^2) := by
    rw [Real.exp_add]
    exact mul_le_mul hqD (treeMomentEnvelope_le_exp D) hB (Real.exp_nonneg _)
  have hPow : (q^D*treeMomentEnvelope D)^M ≤ Real.exp z := by
    unfold z
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by unfold q; positivity) hBase _
  have hZ : 0 ≤ z := by unfold z; positivity
  have hAll : 1+(q^D*treeMomentEnvelope D)^M ≤ Real.exp (2+z) := by
    rw [Real.exp_add]
    exact (show 1+(q^D*treeMomentEnvelope D)^M ≤ 2*Real.exp z by
      linarith only [hPow, Real.one_le_exp hZ]).trans
      (mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _))
  refine hAll.trans (Real.exp_le_exp.mpr ?_)
  let p := (((D : ℝ)+1)*((M : ℝ)+1))^2
  have hp₀ : (1 : ℝ) ≤ p := by
    unfold p
    have h₁ : (1 : ℝ) ≤ (D : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
    have h₂ : (1 : ℝ) ≤ (M : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h₁ h₂)
  have hp₁ : (M : ℝ)^2*(D : ℝ) ≤ p := by
    unfold p
    rw [mul_pow, mul_comm (((D : ℝ)+1)^2)]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) D]) (by positivity) (by positivity)
  have hp₂ : (M : ℝ)*(D : ℝ)^2 ≤ p := by
    unfold p
    rw [mul_pow, mul_comm (((D : ℝ)+1)^2)]
    exact mul_le_mul (by nlinarith [Nat.cast_nonneg (α := ℝ) M])
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
  change 2+z ≤ 3200*((2 : ℝ)+1)*p
  unfold z
  nlinarith only [hp₀, hp₁, hp₂]

omit [Fintype I] in
theorem average_abs_treeMonomial_le (T : I → RootedTree) (k : I → ZMod n) (D M : ℕ)
    (hD : ∀ i, (T i).nodeCount ≤ D) {d : ℕ} (hd : d ≤ 2*M) (u : Fin d → I) :
    average (fun x ↦ |∏ p, (T (u p)).field x (k (u p))|) ≤ comparisonEnvelope 2 D M := by
  by_cases hdz : d = 0
  · subst d
    simp only [univ_eq_empty, prod_empty, abs_one, average_const]
    exact Real.one_le_exp (by positivity)
  have hM : 0 < M := by omega
  have hE (i : I) :
      average (fun x ↦ ((T i).field x (k i))^(2*M)) ≤
        ((((2*M-1 : ℕ) : ℝ)^D)*treeMomentEnvelope D)^M := by
    have h := average_even_pow_walshCombination_le hM ((T i).fieldCoefficient (k i)) D
      (treeCoefficients_eq_zero_of_degree_gt T k hD i)
    have he (x : InversionClass n → Bool) :
        walshCombination ((T i).fieldCoefficient (k i)) x = (T i).field x (k i) :=
      ((T i).field_walsh_expansion x (k i)).symm
    simp_rw [he] at h
    refine h.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) (average_sq_nonneg _)) ?_ _)
    exact mul_le_mul_of_nonneg_left (average_field_sq_le_envelope (T i) (k i) (hD i)) (by positivity)
  have hPos (x : InversionClass n → Bool) :
      |∏ p, (T (u p)).field x (k (u p))| ≤
        average (fun p ↦ |(T (u p)).field x (k (u p))|^d) := by
    rw [abs_prod]
    exact product_abs_le_average_pow (Nat.pos_of_ne_zero hdz) _
  apply (average_mono hPos).trans
  rw [average_average_comm]
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hdz)
  refine ((average_mono fun i ↦ (average_mono fun x ↦
    abs_pow_le_one_add_even_pow ((T (u i)).field x (k (u i))) hd).trans ?_).trans_eq (average_const _)).trans
    (moment_bound_le_comparisonEnvelope D M)
  rw [average_add, average_const]
  exact add_le_add_right (hE (u i)) _

/-- The absolute polynomial moment is bounded at arbitrary frequencies
by the same envelope and the coefficient sum. -/
theorem average_abs_treePolynomial_le (T : I → RootedTree) (k : I → ZMod n) (D M : ℕ)
    (hD : ∀ i, (T i).nodeCount ≤ D) (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ 2*M) :
    average (fun x ↦ |p.eval (fun i ↦ (T i).field x (k i))|) ≤
      absCoefficientSum p * comparisonEnvelope 2 D M := by
  simp_rw [MvPolynomial.eval_eq']
  refine (average_mono fun x ↦ abs_sum_le_sum_abs _ _).trans ?_
  simp_rw [average_finsetSum, abs_mul, average_mul_left]
  rw [absCoefficientSum, sum_mul]
  refine sum_le_sum fun m hm ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  obtain ⟨u, hu⟩ := exists_monomial_positions m
  simp_rw [← hu]
  exact average_abs_treeMonomial_le T k D M hD ((monomial_degree_le p hm).trans hp) u

end LovaszTheta.Circulant
