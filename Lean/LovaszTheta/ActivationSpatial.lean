module

public import LovaszTheta.ActivationProjection
public import LovaszTheta.ComparisonEnvelope
public import LovaszTheta.LinearTransfer

/-!
# Spatial activation approximation

The Gaussian test is the squared projection error. The regular
frequencies use Gaussian comparison, and the exceptional frequencies
use the hypercontractive bound for the same test.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Classical NNReal Nat

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n] [Nonempty (InversionClass n)]

omit [Nonempty (InversionClass n)] in
private lemma average_growth_tree_le (a : I → ℝ) (T : I → RootedTree) (k : ZMod n)
    {D r : ℕ} (hr : 0 < r) (hD : ∀ i, (T i).nodeCount ≤ D) :
    average (fun x ↦ (1+|treeLinearEvaluation a T x k|)^r) ≤
      comparisonSignGrowth D r (∑ i, |a i|) := by
  let V (x : InversionClass n → Bool) := treeLinearEvaluation a T x k
  let L := ((((2*r-1 : ℕ) : ℝ)^D) * (∑ i, |a i|)^2 * treeMomentEnvelope D)^r
  have hV : average (fun x ↦ V x^(2*r)) ≤ L := by
    simp only [V,treeLinearEvaluation_eq_linearWalsh]
    exact average_linearWalsh_tree_even_pow_le hr a T (fun _ ↦ k) hD
  have hZ : average (fun _ : InversionClass n → Bool ↦ (0 : ℝ)^(2*r)) ≤ L := by
    rw [zero_pow (by omega : 2*r ≠ 0),average_const]
    unfold L treeMomentEnvelope
    positivity
  have h := l2Average_growth_le V (fun _ ↦ 0) r hV hZ
  unfold comparisonSignGrowth
  simp only [abs_zero,add_zero] at h
  have hMean := abs_average_mul_le_l2Average
    (fun x ↦ (1+|V x|)^r) (fun _ ↦ 1)
  simp only [mul_one] at hMean
  refine (le_abs_self _).trans (hMean.trans ?_)
  exact (mul_le_of_le_one_right (l2Average_nonneg _) ((l2Average_const_le 1).trans_eq abs_one)).trans h

/-- The Gaussian coefficient tail controls the spatial mean-square error,
with an explicit comparison and exceptional-frequency error. -/
theorem average_spatial_activationProjection_sub_sq_le (a : I → ℝ) (T : I → RootedTree)
    (D M : ℕ) (hD : ∀ i, (T i).nodeCount ≤ D)
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) → i = j)
    {τ s H C : ℝ} (hτ : 0 < τ) (hs : 1 ≤ s)
    (hVars : s^2 = ∑ i, a i^2) (hH : 0 ≤ H)
    (hAbs : (∑ i, |a i|) ≤ H * 4^D) (hVar : s^2 ≤ H) (hC : 0 ≤ C)
    (hActivation : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j (activation τ) x| ≤ C*(1+|x|)) :
    let K := 8*(Real.sqrt (s^2+4*τ) * (M+1 : ℝ)^4 * (M.factorial : ℝ)+C)^2
    average (fun k : ZMod n ↦ average (fun x ↦
      (activationProjection τ s M (treeLinearEvaluation a T x k) - activation τ (treeLinearEvaluation a T x k))^2)) ≤
        (∑' j : ℕ, activationCoefficient τ s (j+(M+1))^2) +
        K * (comparisonEnvelope H D M / Real.sqrt n +
          comparisonSignGrowth D (2*M+3) (∑ i, |a i|) * (2/(n : ℝ))) := by
  let K := 8*(Real.sqrt (s^2+4*τ) * (M+1 : ℝ)^4 * (M.factorial : ℝ)+C)^2
  let v : ℝ≥0 := ⟨s^2,sq_nonneg _⟩
  let ψ : ℝ → ℝ := fun x ↦ (activationProjection τ s M x - activation τ x)^2
  let g := ∫ x, ψ x ∂gaussianReal 0 v
  let L := comparisonSignGrowth D (2*M+3) (∑ i, |a i|)
  let R := K*(comparisonEnvelope H D M / Real.sqrt n)
  let E (k : ZMod n) := average (fun x ↦ ψ (treeLinearEvaluation a T x k))
  have hK : 0 ≤ K := by unfold K; positivity
  have hg : 0 ≤ g := integral_nonneg (fun x ↦ sq_nonneg _)
  have hR : 0 ≤ R := by unfold R comparisonEnvelope; positivity
  have hL : 0 ≤ L := by unfold L comparisonSignGrowth; positivity
  have hψ : ContDiff ℝ 3 ψ :=
    (((contDiff_activationProjection τ s M).of_le (by simp)).sub (contDiff_activation hτ)).pow 2
  have hGrow (j : ℕ) (hj : j ≤ 3) (x : ℝ) :
      |iteratedDeriv j ψ x| ≤ K*(1+|x|)^(2*M+3) :=
    abs_iteratedDeriv_activationProjection_sub_sq_le hτ hs hC hActivation M hj x
  have hPt (k : ZMod n) :
      E k ≤ g+R + (K*L)*(if ¬RegularFrequency k then 1 else 0) := by
    by_cases hk : RegularFrequency k
    · have h := abs_average_treeTest_sub_le_envelope a T (fun _ ↦ k) D M
        hD (fun _ ↦ hk) (fun i j h _ ↦ hDistinct i j h) H hH hAbs v hVars hVar K hK ψ hψ hGrow
      have he : E k-g ≤ R := (le_abs_self _).trans (by
        simpa only [E,g,R,treeLinearEvaluation_eq_linearWalsh,mul_div_assoc] using h)
      simp only [hk,not_true_eq_false,ite_false,mul_zero,add_zero]
      linarith only [he]
    · rw [ite_eq_left hk,mul_one]
      have hbound (x : ℝ) : ψ x ≤ K*(1+|x|)^(2*M+3) := by
        have h := hGrow 0 (by decide) x
        rw [iteratedDeriv_zero] at h
        exact (le_abs_self _).trans h
      calc
        E k ≤ average (fun x ↦ K*(1+|treeLinearEvaluation a T x k|)^(2*M+3)) :=
          average_mono (fun x ↦ hbound _)
        _ ≤ K*L := by
          rw [average_mul_left]
          exact mul_le_mul_of_nonneg_left (average_growth_tree_le a T k (by omega) hD) hK
        _ ≤ _ := le_add_of_nonneg_left (add_nonneg hg hR)
  change average E ≤ _
  have hGauss : g = ∑' j : ℕ, activationCoefficient τ s (j+(M+1))^2 :=
    integral_activationProjection_sub_sq hτ.le (by linarith) M
  calc
    _ ≤ average (fun k ↦ g+R+(K*L)*(if ¬RegularFrequency k then 1 else 0)) :=
      average_mono hPt
    _ ≤ g+R+(K*L)*(2/(n : ℝ)) := by
      rw [average_add,average_const,average_mul_left]
      exact add_le_add_right (mul_le_mul_of_nonneg_left average_not_regularFrequency_le (mul_nonneg hK hL)) _
    _ = _ := by rw [hGauss]; unfold R L; ring

end LovaszTheta.Circulant
