module

public import LovaszTheta.ActivationDerivatives
public import LovaszTheta.HermiteActivationEnergy

/-!
# High-order Hermite tails and offspring moments

Repeated integration by parts weights each coefficient by a falling
factorial. Parseval for the derivative bounds those weighted sums
uniformly in the Gaussian scale.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace LovaszTheta.Circulant

private lemma contDiff_scaled_activation {τ : ℝ} (hτ : 0 < τ) (σ : ℝ) (j : ℕ) :
    ContDiff ℝ j (fun x ↦ activation τ (σ*x)) :=
  (contDiff_activation hτ).comp (by fun_prop)

private lemma growth_iteratedDeriv_scaled_activation {τ σ : ℝ} (hτ : 0 < τ)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (j : ℕ) :
    HasPolynomialGrowth (iteratedDeriv j (fun x ↦ activation τ (σ*x))) := by
  by_cases hj : j = 0
  · rw [hj, iteratedDeriv_zero]
    exact hasPolynomialGrowth_scaled_activation hτ.le σ
  · obtain ⟨C, hC, h⟩ := exists_bound_abs_iteratedDeriv_scaled_activation hτ (Nat.pos_of_ne_zero hj)
    exact HasPolynomialGrowth.of_bound hC (h σ hσ hσ')

private lemma hermiteCoefficient_iteratedDeriv_sq (f : ℝ → ℝ)
    (hDiff : ∀ j : ℕ, ContDiff ℝ j f)
    (hGrow : ∀ j, HasPolynomialGrowth (iteratedDeriv j f)) (p j : ℕ) :
    hermiteCoefficient (iteratedDeriv p f) j ^ 2 =
      (((j+p).descFactorial p : ℕ) : ℝ) * hermiteCoefficient f (j+p)^2 := by
  induction p generalizing j with
  | zero => simp [iteratedDeriv_zero]
  | succ p ih =>
    have hCD : ContDiff ℝ ((p : WithTop ℕ∞)+1) f := by
      simpa only [Nat.cast_add, Nat.cast_one] using hDiff (p+1)
    have hd (x : ℝ) : HasDerivAt (iteratedDeriv p f) (iteratedDeriv (p+1) f x) x := by
      rw [iteratedDeriv_succ]
      exact (hCD.differentiable_iteratedDeriv' p x).hasDerivAt
    have hShift := hermiteCoefficient_derivative j hd
      ((hDiff (p+1)).continuous_iteratedDeriv' (p+1)) (hGrow p) (hGrow (p+1))
    rw [hShift, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (j : ℝ)+1), ih,
      Nat.descFactorial_succ, show j+(p+1)-p = j+1 by omega, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      show j+1+p = j+(p+1) by omega, mul_assoc]

/-- The falling-factorial weighted coefficient sum is bounded uniformly
for the scales up to the upper variance bound of the Gaussian equation. -/
theorem exists_weighted_activationCoefficient_bound {τ : ℝ} (hτ : 0 < τ) {p : ℕ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ Real.sqrt (2*Real.pi) →
      ∃ e : ℝ, HasSum
        (fun j : ℕ ↦ (((j+p).descFactorial p : ℕ) : ℝ) * activationCoefficient τ σ (j+p)^2) e ∧ e ≤ C := by
  obtain ⟨K, hK, hDer⟩ := exists_bound_abs_iteratedDeriv_scaled_activation hτ hp
  refine ⟨K^2, sq_nonneg _, fun σ hσ hσ' ↦ ?_⟩
  let f (x : ℝ) := activation τ (σ*x)
  let d := iteratedDeriv p f
  have hF := contDiff_scaled_activation hτ σ
  have hG := growth_iteratedDeriv_scaled_activation hτ hσ hσ'
  have hC : Continuous d := (hF p).continuous_iteratedDeriv' p
  have hLp := (hG p).memLp_gaussian_two hC 1
  have hP := hasSum_sq_hermiteCoefficient hLp
  refine ⟨∫ x, d x^2 ∂gaussianReal 0 1, ?_, ?_⟩
  · have he (j : ℕ) := hermiteCoefficient_iteratedDeriv_sq f hF hG p j
    simpa only [d, he, activationCoefficient, f] using hP
  · have hi := (memLp_two_iff_integrable_sq hC.aestronglyMeasurable).mp hLp
    have hPt (x : ℝ) : d x^2 ≤ K^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hDer σ hσ hσ' x) _
    simpa [Measure.real] using integral_mono hi (integrable_const _) hPt

private lemma half_pow_le_descFactorial (n p : ℕ) (h : 2*p ≤ n) :
    ((n : ℝ)/2)^p ≤ (n.descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, Nat.descFactorial_succ, Nat.cast_mul]
    have hn : p ≤ n := by omega
    have hnp : (n : ℝ)/2 ≤ ((n-p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]
      have he : (2 : ℝ)*((p : ℝ)+1) ≤ n := by exact_mod_cast h
      linarith
    rw [mul_comm (((n-p : ℕ) : ℝ))]
    exact mul_le_mul (ih (by omega)) hnp (by positivity) (by positivity)

/-- The squared Hermite tail decays faster than each fixed power of
the degree cutoff, uniformly over the admissible Gaussian scales. -/
theorem activationCoefficient_sq_tail_le {τ : ℝ} (hτ : 0 < τ) {p : ℕ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ Real.sqrt (2*Real.pi) →
      ∀ M : ℕ, 2*p ≤ M →
      (∑' j : ℕ, activationCoefficient τ σ (j+(M+1))^2) ≤ C/(M : ℝ)^p := by
  obtain ⟨K, hK, hBound⟩ := exists_weighted_activationCoefficient_bound hτ hp
  refine ⟨(2 : ℝ)^p*K, by positivity, fun σ hσ hσ' M hM ↦ ?_⟩
  obtain ⟨e, hsum, he⟩ := hBound σ hσ hσ'
  let q := M+1-p
  let F (j : ℕ) := (((j+p).descFactorial p : ℕ) : ℝ) * activationCoefficient τ σ (j+p)^2
  let G (j : ℕ) := activationCoefficient τ σ (j+(M+1))^2
  let b := ((M : ℝ)/2)^p
  have hQ (j : ℕ) : j+q+p = j+(M+1) := by unfold q; omega
  have hFn (j : ℕ) : 0 ≤ F j := by unfold F; positivity
  have hS : Summable G :=
    ((hasSum_nat_add_iff' (M+1)).mpr (hasSum_activationCoefficient_sq hτ.le σ)).summable
  have hTail := (hasSum_nat_add_iff' q).mpr (show HasSum F e from hsum)
  have hPt (j : ℕ) : b*G j ≤ F (j+q) := by
    unfold F G
    rw [hQ]
    have hW := half_pow_le_descFactorial (j+(M+1)) p (by omega)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (pow_le_pow_left₀ (by positivity) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) _).trans hW
  have hCmp := Summable.tsum_le_tsum hPt (hS.mul_left b) hTail.summable
  rw [tsum_mul_left, hTail.tsum_eq] at hCmp
  have hSum := (hCmp.trans (sub_le_self _ (sum_nonneg fun j _ ↦ hFn j))).trans he
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  apply (le_div_iff₀ (pow_pos hMpos p)).mpr
  have hb : b*(2 : ℝ)^p = (M : ℝ)^p := by unfold b; rw [div_pow, div_mul_cancel₀ _ (by positivity)]
  calc
    _ = (2 : ℝ)^p*(b*∑' j, G j) := by rw [← mul_assoc, mul_comm ((2 : ℝ)^p), hb, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hSum (by positivity)

/-- All polynomial moments of the subcritical offspring distribution are finite. -/
theorem summable_gaussianOffspringProbability_moment {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) (p : ℕ) :
    Summable (fun j : ℕ ↦ (j : ℝ)^p*gaussianOffspringProbability τ σ j) := by
  by_cases hp : p = 0
  · simpa only [hp, pow_zero, one_mul] using
      (gaussianOffspringProbability_mass_and_mean hτ hσ hMean).1.summable
  obtain ⟨_, _, hBound⟩ := exists_weighted_activationCoefficient_bound hτ (Nat.pos_of_ne_zero hp)
  obtain ⟨e, he, _⟩ := hBound σ hσ.le hσ'
  let F (j : ℕ) := (((j+p).descFactorial p : ℕ) : ℝ)*activationCoefficient τ σ (j+p)^2
  let c := (2 : ℝ)^p / σ^2
  have hs : Summable (fun j ↦ c*F (j+p)) :=
    ((hasSum_nat_add_iff' p).mpr (show HasSum F e from he)).summable.mul_left c
  apply (summable_nat_add_iff (2*p)).mp
  apply Summable.of_nonneg_of_le _ _ hs
  · exact fun j ↦ mul_nonneg (by positivity) (gaussianOffspringProbability_nonneg τ σ (j+2*p))
  · intro j
    let m := j+2*p
    have hm : (j+p)+p = m := by unfold m; omega
    have hm₀ : m ≠ 0 := by unfold m; omega
    change (m : ℝ)^p*gaussianOffspringProbability τ σ m ≤ c*F (j+p)
    unfold gaussianOffspringProbability c F
    rw [ite_eq_right hm₀, hm]
    have hn := half_pow_le_descFactorial m p (by unfold m; omega)
    have hP : (m : ℝ)^p ≤ (2 : ℝ)^p*(m.descFactorial p : ℝ) := by
      rw [div_pow, div_le_iff₀ (by positivity), mul_comm] at hn
      exact hn
    calc
      _ ≤ ((2 : ℝ)^p*(m.descFactorial p : ℝ))*(activationCoefficient τ σ m^2/σ^2) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = _ := by ring

end LovaszTheta.Circulant
