module

public import LovaszTheta.GaussianActivationSeries
public import LovaszTheta.HermitePowerExpansion
public import LovaszTheta.HermiteActivationTail

/-!
# Finite Hermite projection of the activation

The error under the Gaussian law is the squared tail of the Hermite
coefficients. The factorial coefficient bound gives a polynomial
growth estimate for the squared error and its first three derivatives.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Nat NNReal

namespace LovaszTheta.Circulant

/-- The degree-cutoff Hermite projection under a centered Gaussian of scale `s`. -/
noncomputable def activationProjection (τ s : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (M+1), activationCoefficient τ s j * normalizedHermite j (x/s)

private lemma activationProjection_scaled {τ s : ℝ} (hs : s ≠ 0) (M : ℕ) (x : ℝ) :
    activationProjection τ s M (s*x) =
      ∑ j ∈ range (M+1), activationCoefficient τ s j * normalizedHermite j x := by
  simp only [activationProjection,mul_div_cancel_left₀ _ hs]

/-- The projection is smooth, as it is a finite sum of polynomials. -/
lemma contDiff_activationProjection (τ s : ℝ) (M : ℕ) : ContDiff ℝ ∞ (activationProjection τ s M) := by
  unfold activationProjection
  simp_rw [normalizedHermite_eq_sum_powers]
  fun_prop

/-- The squared coefficient sum of the projection does not exceed the activation energy. -/
theorem sum_sq_activationCoefficient_le {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ) (M : ℕ) :
    (∑ j ∈ range (M+1), activationCoefficient τ s j ^ 2) ≤ s^2 + 4*τ := by
  have h := hasSum_activationCoefficient_sq hτ s
  exact (h.summable.sum_le_tsum _ (fun _ _ ↦ sq_nonneg _)).trans_eq h.tsum_eq

lemma abs_activationCoefficient_le {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ) (j : ℕ) :
    |activationCoefficient τ s j| ≤ Real.sqrt (s^2+4*τ) := by
  have h := hasSum_activationCoefficient_sq hτ s
  have hh := (h.summable.le_tsum j (fun _ _ ↦ sq_nonneg _)).trans_eq h.tsum_eq
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hh

/-- The projection error in the Gaussian law is exactly the squared Hermite tail. -/
theorem integral_activationProjection_sub_sq {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) (M : ℕ) :
    (∫ x, (activationProjection τ s M x - activation τ x)^2
      ∂gaussianReal 0 ⟨s^2,sq_nonneg s⟩) =
      ∑' j : ℕ, activationCoefficient τ s (j+(M+1))^2 := by
  let p (x : ℝ) := ∑ j ∈ range (M+1), activationCoefficient τ s j * normalizedHermite j x
  let f (x : ℝ) := activation τ (s*x)
  have hp : MemLp p 2 (gaussianReal 0 1) :=
    memLp_finsetSum _ (fun j _ ↦ (memLp_normalizedHermite j).const_mul _)
  have hf : MemLp f 2 (gaussianReal 0 1) := memLp_scaledActivation hτ s
  have hCoeff (i : ℕ) : hermiteCoefficient (fun x ↦ p x - f x) i =
      if i < M+1 then 0 else -activationCoefficient τ s i := by
    unfold hermiteCoefficient
    simp_rw [sub_mul]
    have hp' : Integrable (fun x ↦ p x*normalizedHermite i x) (gaussianReal 0 1) :=
      hp.integrable_mul (memLp_normalizedHermite i)
    have hf' : Integrable (fun x ↦ f x*normalizedHermite i x) (gaussianReal 0 1) :=
      hf.integrable_mul (memLp_normalizedHermite i)
    rw [integral_sub hp' hf']
    have h₁ : (∫ x, p x*normalizedHermite i x ∂gaussianReal 0 1) =
        if i < M+1 then activationCoefficient τ s i else 0 := by
      simp_rw [p,sum_mul,mul_assoc]
      have hInt (j : ℕ) : Integrable (fun x ↦ activationCoefficient τ s j *
          (normalizedHermite j x * normalizedHermite i x)) (gaussianReal 0 1) :=
        ((memLp_normalizedHermite j).integrable_mul (memLp_normalizedHermite i)).const_mul _
      rw [integral_finsetSum _ fun j _ ↦ hInt j]
      simp only [integral_const_mul,integral_normalizedHermite_mul,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',mem_range]
    rw [h₁]
    change (if i < M+1 then _ else 0) - activationCoefficient τ s i = _
    split_ifs <;> ring
  have hS := hasSum_sq_hermiteCoefficient (hp.sub hf)
  change HasSum (fun i ↦ hermiteCoefficient (fun x ↦ p x-f x) i ^ 2)
    (∫ x, (p x-f x)^2 ∂gaussianReal 0 1) at hS
  simp only [hCoeff] at hS
  have he := (hasSum_nat_add_iff' (M+1)).mpr hS
  have hzero : (∑ i ∈ range (M+1),
    (if i < M+1 then 0 else -activationCoefficient τ s i)^2) = 0 :=
    sum_eq_zero fun i hi ↦ by rw [ite_eq_left (mem_range.mp hi),zero_pow (by decide)]
  simp only [hzero,sub_zero,show ∀ j : ℕ, ¬j+(M+1)<M+1 by omega,ite_false,neg_sq] at he
  have hMap : (gaussianReal 0 1).map (fun x ↦ s*x) = gaussianReal 0 ⟨s^2,sq_nonneg s⟩ := by
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
  have hpCont : Continuous (fun x ↦ (activationProjection τ s M x-activation τ x)^2) :=
    (((contDiff_activationProjection τ s M).continuous).sub (continuous_activation τ)).pow 2
  rw [← hMap,integral_map (by fun_prop) hpCont.aestronglyMeasurable]
  simpa only [activationProjection_scaled hs.ne',p,f] using he.tsum_eq.symm

private lemma abs_iteratedDeriv_scaledHermite_le {s : ℝ} (hs : 1 ≤ s)
    {i M j : ℕ} (hi : i ≤ M) (hj : j ≤ 3) (x : ℝ) :
    |iteratedDeriv j (fun y ↦ normalizedHermite i (y/s)) x| ≤
      (M+1 : ℝ)^3 * (M.factorial : ℝ) * (1+|x|)^M := by
  have hExp : (fun y : ℝ ↦ normalizedHermite i (y/s)) =
      fun y ↦ ∑ r : Fin (i+1), (hermitePowerCoeff i r.val / s^r.val) * y^r.val := by
    funext y
    rw [normalizedHermite_eq_sum_powers]
    exact sum_congr rfl fun r _ ↦ by rw [div_pow]; ring
  rw [hExp,iteratedDeriv_fun_sum (fun _ _ ↦ by fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hPt (r : Fin (i+1)) :
      |hermitePowerCoeff i r.val / s^r.val * ((r.val.descFactorial j : ℕ) * x^(r.val-j))| ≤
        |hermitePowerCoeff i r.val| * ((M+1 : ℝ)^3 * (1+|x|)^M) := by
    have hr : r.val ≤ M := (Nat.le_of_lt_succ r.isLt).trans hi
    have hF : (r.val.descFactorial j : ℝ) ≤ (M+1 : ℝ)^3 := by
      refine (show (r.val.descFactorial j : ℝ) ≤ (r.val : ℝ)^j by
        exact_mod_cast Nat.descFactorial_le_pow r.val j).trans ?_
      have hL : (r.val : ℝ) ≤ (M+1 : ℝ) := by exact_mod_cast (show r.val ≤ M+1 by omega)
      exact (pow_le_pow_left₀ (by positivity) hL _).trans (pow_right_mono₀ (by linarith [Nat.cast_nonneg (α := ℝ) M] : 1 ≤ (M+1 : ℝ)) hj)
    have hP : |x|^(r.val-j) ≤ (1+|x|)^M :=
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |x| ≤ 1+|x|) _).trans
        (pow_right_mono₀ (by linarith [abs_nonneg x] : 1 ≤ 1+|x|) (by omega))
    simp only [abs_mul,abs_div,abs_pow,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),abs_of_nonneg (by linarith : 0 ≤ s)]
    exact mul_le_mul (div_le_self (abs_nonneg _) (one_le_pow₀ hs)) (mul_le_mul hF hP (by positivity) (by positivity))
      (by positivity) (abs_nonneg _)
  calc
    _ ≤ ∑ r : Fin (i+1), |hermitePowerCoeff i r.val| * ((M+1 : ℝ)^3 * (1+|x|)^M) :=
      sum_le_sum fun r _ ↦ hPt r
    _ ≤ _ := by
      rw [← sum_mul,mul_right_comm ((M+1 : ℝ)^3),mul_comm _ (M.factorial : ℝ)]
      have hFact : (i.factorial : ℝ) ≤ (M.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hi
      exact mul_le_mul_of_nonneg_right
        ((sum_abs_hermitePowerCoeff_le i).trans hFact) (by positivity : 0 ≤ (M+1 : ℝ)^3 * (1+|x|)^M)

/-- A bound on derivatives of the projection in terms of the Gaussian energy. -/
theorem abs_iteratedDeriv_activationProjection_le {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 1 ≤ s)
    (M : ℕ) {j : ℕ} (hj : j ≤ 3) (x : ℝ) :
    |iteratedDeriv j (activationProjection τ s M) x| ≤
      (Real.sqrt (s^2+4*τ) * (M+1 : ℝ)^4 * (M.factorial : ℝ)) * (1+|x|)^M := by
  unfold activationProjection
  rw [iteratedDeriv_fun_sum (fun i _ ↦ by simp_rw [normalizedHermite_eq_sum_powers]; fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp_rw [abs_mul]
  calc
    _ ≤ ∑ i ∈ range (M+1), Real.sqrt (s^2+4*τ) * ((M+1 : ℝ)^3 * (M.factorial : ℝ) * (1+|x|)^M) := by
      exact sum_le_sum fun i hi ↦ mul_le_mul (abs_activationCoefficient_le hτ s i)
        (abs_iteratedDeriv_scaledHermite_le hs (Nat.le_of_lt_succ (mem_range.mp hi)) hj x)
        (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

/-- A single constant bounds the activation and its first three derivatives. -/
theorem exists_activation_derivatives_le {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j (activation τ) x| ≤ C*(1+|x|) := by
  obtain ⟨A,hA,h₁⟩ := exists_bound_abs_iteratedDeriv_activation (j := 1) hτ (by decide)
  obtain ⟨B,hB,h₂⟩ := exists_bound_abs_iteratedDeriv_activation (j := 2) hτ (by decide)
  obtain ⟨C,hC,h₃⟩ := exists_bound_abs_iteratedDeriv_activation (j := 3) hτ (by decide)
  let K := 1+2*Real.sqrt τ+A+B+C
  have hK : 0 ≤ K := by unfold K; positivity
  refine ⟨K,hK,fun j hj x ↦ ?_⟩
  have hX : 1 ≤ 1+|x| := by linarith [abs_nonneg x]
  have hGrow : K ≤ K*(1+|x|) := le_mul_of_one_le_right hK hX
  interval_cases j
  · rw [iteratedDeriv_zero,abs_of_nonneg (activation_nonneg τ x)]
    refine (activation_le_abs_add hτ.le x).trans ?_
    have he : 1+2*Real.sqrt τ ≤ K := by dsimp only [K]; linarith
    exact (show |x|+2*Real.sqrt τ ≤ (1+2*Real.sqrt τ)*(1+|x|) by nlinarith [mul_nonneg (Real.sqrt_nonneg τ) (abs_nonneg x)]).trans
      (mul_le_mul_of_nonneg_right he (by positivity))
  · exact (h₁ x).trans ((show A ≤ K by dsimp only [K]; linarith [Real.sqrt_nonneg τ]).trans hGrow)
  · exact (h₂ x).trans ((show B ≤ K by dsimp only [K]; linarith [Real.sqrt_nonneg τ]).trans hGrow)
  · exact (h₃ x).trans ((show C ≤ K by dsimp only [K]; linarith [Real.sqrt_nonneg τ]).trans hGrow)

/-- Product differentiation gives the growth condition for the Gaussian comparison test. -/
theorem abs_iteratedDeriv_activationProjection_sub_sq_le {τ s C : ℝ}
    (hτ : 0 < τ) (hs : 1 ≤ s) (hC : 0 ≤ C)
    (hActivation : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j (activation τ) x| ≤ C*(1+|x|))
    (M : ℕ) {j : ℕ} (hj : j ≤ 3) (x : ℝ) :
    |iteratedDeriv j (fun y ↦ (activationProjection τ s M y - activation τ y)^2) x| ≤
      8*(Real.sqrt (s^2+4*τ) * (M+1 : ℝ)^4 * (M.factorial : ℝ)+C)^2*(1+|x|)^(2*M+3) := by
  let P := activationProjection τ s M
  let f : ℝ → ℝ := fun y ↦ P y - activation τ y
  let A := Real.sqrt (s^2+4*τ) * (M+1 : ℝ)^4 * (M.factorial : ℝ)
  let L := 1+|x|
  have hL : 1 ≤ L := by unfold L; linarith [abs_nonneg x]
  have hDiff : ContDiff ℝ ∞ f := (contDiff_activationProjection τ s M).sub (contDiff_activation hτ)
  have hBd (i : ℕ) (hi : i ≤ 3) : |iteratedDeriv i f x| ≤ (A+C)*L^(M+1) := by
    unfold f
    rw [iteratedDeriv_fun_sub
      (((contDiff_activationProjection τ s M).of_le (by simp) : ContDiff ℝ i P).contDiffAt)
      ((contDiff_activation (r := i) hτ).contDiffAt)]
    refine (abs_sub _ _).trans ?_
    rw [add_mul]
    apply add_le_add
    · exact (abs_iteratedDeriv_activationProjection_le hτ.le hs M hi x).trans
        (mul_le_mul_of_nonneg_left (pow_right_mono₀ hL (Nat.le_succ _)) (by positivity))
    · refine (hActivation i hi x).trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact (pow_one L).ge.trans (pow_right_mono₀ hL (by omega : 1 ≤ M+1))
  change |iteratedDeriv j (fun y ↦ f y ^ 2) x| ≤ 8*(A+C)^2*L^(2*M+3)
  simp only [pow_two]
  have hAt : ContDiffAt ℝ j f x := (hDiff.of_le (by simp)).contDiffAt
  rw [iteratedDeriv_fun_mul hAt hAt]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  have hSquare : ((A+C)*L^(M+1))^2 ≤ (A+C)^2*L^(2*M+3) := by
    rw [mul_pow,← pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_right_mono₀ hL (by omega)) (sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ range (j+1), (j.choose i : ℝ) * ((A+C)^2*L^(2*M+3)) := by
      apply sum_le_sum
      intro i hi
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul (hBd i (by have := mem_range.mp hi; omega)) (hBd (j-i) (by omega))
        (abs_nonneg _) ((abs_nonneg _).trans (hBd i (by have := mem_range.mp hi; omega)))).trans_eq (by ring)
        |>.trans hSquare
    _ ≤ _ := by
      rw [← sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
      have h : (2 : ℝ)^j ≤ 8 :=
        (pow_right_mono₀ (by norm_num : 1 ≤ (2 : ℝ)) hj).trans_eq (by norm_num)
      exact (mul_le_mul_of_nonneg_right h (by positivity)).trans_eq (by ring)

end LovaszTheta.Circulant
