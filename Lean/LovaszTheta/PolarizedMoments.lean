module

public import LovaszTheta.ComparisonEnvelope
public import LovaszTheta.GaussianCoordinates
public import LovaszTheta.Polarization

/-!
# Monomial tests in the Gaussian comparison

The polarized linear forms have coefficient absolute sum at most
one, even when several positions represent the same coordinate.
Their power tests satisfy the smooth comparison.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I]

/-- The normalized coefficients of a signed combination of monomial positions. -/
noncomputable def polarizedCoefficients {d : ℕ} (u : Fin d → I) (η : Fin d → Bool) (i : I) : ℝ :=
  (∑ p with u p = i, sign (η p)) / (d : ℝ)

lemma polarizedCoefficients_sum_mul {d : ℕ} (u : Fin d → I) (η : Fin d → Bool) (x : I → ℝ) :
    (∑ i, polarizedCoefficients u η i * x i) = (∑ p, sign (η p)*x (u p)) / (d : ℝ) := by
  unfold polarizedCoefficients
  simp_rw [div_mul_eq_mul_div, sum_mul, sum_div]
  simp_rw [sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun p _ ↦ by simp

lemma sum_abs_polarizedCoefficients_le {d : ℕ} (u : Fin d → I) (η : Fin d → Bool) :
    (∑ i, |polarizedCoefficients u η i|) ≤ 1 := by
  by_cases hd : d = 0
  · simp [polarizedCoefficients, hd]
  have h (i : I) :
      |∑ p with u p = i, sign (η p)| ≤ ∑ p : Fin d with u p = i, (1 : ℝ) := by
    exact (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun p _ ↦ abs_sign (η p))
  have hSum : (∑ i, ∑ p : Fin d with u p = i, (1 : ℝ)) = d := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  unfold polarizedCoefficients
  simp only [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d), ← sum_div]
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [div_le_iff₀ hd', one_mul, ← hSum]
  exact sum_le_sum fun i _ ↦ h i

private lemma sum_sq_le_sq_sum_abs (a : I → ℝ) : (∑ i, a i^2) ≤ (∑ i, |a i|)^2 := by
  rw [pow_two, sum_mul]
  apply sum_le_sum
  intro i _
  rw [← sq_abs (a i), pow_two]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ ↦ abs_nonneg (a j)) (mem_univ i)) (abs_nonneg _)

private lemma abs_iteratedDeriv_pow_le {d M : ℕ} (hM : d ≤ 2*M) {j : ℕ} (hj : j ≤ 3) (x : ℝ) :
    |iteratedDeriv j (fun z : ℝ ↦ z^d) x| ≤ ((d : ℝ)+1)^3 * (1+|x|)^(2*M+3) := by
  rw [iteratedDeriv_pow, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_pow]
  have hCoef : ((d.descFactorial j : ℕ) : ℝ) ≤ ((d : ℝ)+1)^3 := by
    have h := Nat.descFactorial_le_pow d j
    refine (show ((d.descFactorial j : ℕ) : ℝ) ≤ (d : ℝ)^j by exact_mod_cast h).trans ?_
    exact (pow_le_pow_left₀ (by positivity) (by linarith : (d : ℝ) ≤ (d : ℝ)+1) j).trans
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d]) hj)
  have hPow : |x|^(d-j) ≤ (1+|x|)^(2*M+3) :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |x| ≤ 1+|x|) _).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by omega))
  exact mul_le_mul hCoef hPow (by positivity) (by positivity)

lemma average_average_comm {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    average (fun x ↦ average (f x)) = average (fun y ↦ average (fun x ↦ f x y)) := by
  unfold average
  simp only [← sum_div]
  rw [sum_comm]
  ring

private lemma integral_average_comm {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (μ : Measure X) (f : Ω → X → ℝ) (hf : ∀ x, Integrable (f x) μ) :
    (∫ z, average (fun x ↦ f x z) ∂μ) = average (fun x ↦ ∫ z, f x z ∂μ) := by
  simp only [average, integral_div, integral_finsetSum _ fun x _ ↦ hf x]

private lemma integrable_gaussianLinear_pow (a : I → ℝ) (d : ℕ) :
    Integrable (fun x ↦ (∑ i, a i*x i)^d) (gaussianCoordinates I) := by
  have hm := measurable_coordinate_sum a
  have hf : Continuous (fun z : ℝ ↦ z^d) := by fun_prop
  refine (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp ?_
  rw [map_gaussianCoordinates_sum]
  exact integrable_growth_gaussian _ d 1 hf fun x ↦ by
    rw [one_mul, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _

/-- Integrability of the monomial follows by its finite polarization. -/
lemma integrable_gaussianCoordinates_monomial {d : ℕ} (u : Fin d → I) :
    Integrable (fun x ↦ ∏ p, x (u p)) (gaussianCoordinates I) := by
  let F (η : Fin d → Bool) (x : I → ℝ) :=
    walsh univ η * (∑ i, polarizedCoefficients u η i * x i)^d
  have hi (η : Fin d → Bool) : Integrable (F η) (gaussianCoordinates I) :=
    (integrable_gaussianLinear_pow (polarizedCoefficients u η) d).const_mul _
  have h : Integrable (fun x ↦ average (fun η ↦ F η x)) (gaussianCoordinates I) :=
    (integrable_finsetSum univ (fun η _ ↦ hi η)).div_const _
  refine (h.const_mul ((d : ℝ)^d / d.factorial)).congr (ae_of_all _ fun x ↦ ?_)
  symm
  simpa only [F, polarizedCoefficients_sum_mul] using prod_eq_polarized_average (fun p ↦ x (u p))

private lemma abs_walsh_eq_one {d : ℕ} (η : Fin d → Bool) : |walsh univ η| = 1 := by
  simp [walsh, abs_prod]

private lemma polarization_factor_le {d D M : ℕ} (hd : d ≤ 2*M) :
    ((d : ℝ)^d / d.factorial) * ((d : ℝ)+1)^3 * comparisonEnvelope 1 D M ≤
      comparisonEnvelope 2 D M := by
  let p := (((D : ℝ)+1)*((M : ℝ)+1))^2
  have hδ : (1 : ℝ) ≤ (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hA : (d : ℝ)^d / d.factorial ≤ Real.exp ((d : ℝ)^2) := by
    apply (div_le_self (by positivity) hδ).trans
    rw [pow_two, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [Real.add_one_le_exp (d : ℝ)]) _
  have hB : ((d : ℝ)+1)^3 ≤ Real.exp (3*((d : ℝ)+1)) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (d : ℝ)+1) (Real.add_one_le_exp (d : ℝ)) 3
    rw [← Real.exp_nat_mul] at h
    exact h.trans (Real.exp_le_exp.mpr (by push_cast; linarith))
  have hP : ((M : ℝ)+1)^2 ≤ p := by
    unfold p
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) D])
  have hdR : (d : ℝ) ≤ 2*(M : ℝ) := by exact_mod_cast hd
  have hdSq : (d : ℝ)^2 ≤ (2*(M : ℝ))^2 := pow_le_pow_left₀ (by positivity) hdR _
  have hAB := mul_le_mul hA hB (by positivity) (Real.exp_nonneg _)
  rw [← Real.exp_add] at hAB
  unfold comparisonEnvelope
  calc
    _ ≤ Real.exp ((d : ℝ)^2+3*((d : ℝ)+1))*Real.exp (3200*((1 : ℝ)+1)*p) :=
      mul_le_mul_of_nonneg_right hAB (Real.exp_nonneg _)
    _ = Real.exp (((d : ℝ)^2+3*((d : ℝ)+1))+3200*((1 : ℝ)+1)*p) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change _ ≤ 3200*((2 : ℝ)+1)*p
      nlinarith only [hP, hdR, hdSq, Nat.cast_nonneg (α := ℝ) M]

variable {n : ℕ} [NeZero n] [Nonempty (InversionClass n)]

/-- The regular-frequency comparison for a monomial in a finite family
of tree coordinates. Repeated indices in the monomial are allowed. -/
theorem abs_average_treeMonomial_sub_gaussian_le (T : I → RootedTree) (k : I → ZMod n)
    (D M : ℕ) (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j)
    {d : ℕ} (hd : d ≤ 2*M) (u : Fin d → I) :
    |average (fun x ↦ ∏ p, (T (u p)).field x (k (u p))) -
      (∫ x, ∏ p, x (u p) ∂gaussianCoordinates I)| ≤
      comparisonEnvelope 2 D M / Real.sqrt n := by
  let W (η : Fin d → Bool) := walsh univ η
  let a (η : Fin d → Bool) := polarizedCoefficients u η
  let V (η : Fin d → Bool) (x : InversionClass n → Bool) := linearWalsh (a η) (treeCoefficients T k) x
  let G (η : Fin d → Bool) (x : I → ℝ) := ∑ i, a η i*x i
  let K := (d : ℝ)^d / d.factorial
  have hκ : 0 ≤ K := by unfold K; positivity
  have hV (x : InversionClass n → Bool) :
      (∏ p, (T (u p)).field x (k (u p))) = K * average (fun η ↦ W η*(V η x)^d) := by
    simpa only [K, W, V, a, linearWalsh_treeCoefficients, polarizedCoefficients_sum_mul] using
      prod_eq_polarized_average (fun p ↦ (T (u p)).field x (k (u p)))
  have hG (x : I → ℝ) :
      (∏ p, x (u p)) = K * average (fun η ↦ W η*(G η x)^d) := by
    simpa only [K, W, G, a, polarizedCoefficients_sum_mul] using prod_eq_polarized_average (fun p ↦ x (u p))
  have hGint (η : Fin d → Bool) : Integrable (fun x ↦ W η*(G η x)^d) (gaussianCoordinates I) :=
    (integrable_gaussianLinear_pow (a η) d).const_mul (W η)
  simp_rw [hV, hG, average_mul_left K, integral_const_mul]
  rw [average_average_comm (fun x η ↦ W η*(V η x)^d),
    integral_average_comm (gaussianCoordinates I) _ hGint]
  simp_rw [average_mul_left, integral_const_mul, ← mul_sub, ← average_sub, ← mul_sub]
  rw [abs_mul, abs_of_nonneg hκ]
  let C := ((d : ℝ)+1)^3
  have hPoint (η : Fin d → Bool) :
      |W η * (average (fun x ↦ (V η x)^d) - (∫ x, (G η x)^d ∂gaussianCoordinates I))| ≤
        C*comparisonEnvelope 1 D M/Real.sqrt n := by
    let v := (∑ i, (a η i)^2).toNNReal
    have hv : (v : ℝ) = ∑ i, (a η i)^2 := Real.coe_toNNReal _ (by positivity)
    have hℓ : (∑ i, |a η i|) ≤ 1 := sum_abs_polarizedCoefficients_le u η
    have hv₁ : (v : ℝ) ≤ 1 := by
      rw [hv]
      exact (sum_sq_le_sq_sum_abs (a η)).trans (by
        simpa only [one_pow] using pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ abs_nonneg _) hℓ 2)
    simp only [abs_mul, W, abs_walsh_eq_one, one_mul]
    change |average (fun x ↦ (V η x)^d) - (∫ x, (fun z : ℝ ↦ z^d) (G η x) ∂gaussianCoordinates I)| ≤ _
    rw [integral_test_gaussianCoordinates_sum (a η) (by fun_prop : Measurable fun z : ℝ ↦ z^d)]
    exact abs_average_treeTest_sub_le_envelope (a η) T k D M hD hk hDistinct 1 zero_le_one
      (hℓ.trans (by simpa only [one_mul] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)))
      v hv hv₁ C (by unfold C; positivity) (fun z ↦ z^d) (by fun_prop)
      (fun _ hj x ↦ abs_iteratedDeriv_pow_le hd hj x)
  refine (mul_le_mul_of_nonneg_left ((abs_average_le_average_abs _).trans
    ((average_mono hPoint).trans_eq (average_const _))) hκ).trans ?_
  rw [← mul_div_assoc, ← mul_assoc]
  exact div_le_div_of_nonneg_right (polarization_factor_le hd) (Real.sqrt_nonneg _)

end LovaszTheta.Circulant
