module

public import LovaszTheta.MatrixWitness

/-!
# The independent-edge expectation limit

On the witness event, use the shifted polynomial certificate.
On its complement, the elementary bound by the vertex count
makes the exceptional contribution vanish. The ratio of the
constant and single-edge coefficients approaches one.
-/

@[expose] public section

open Filter Finset
open scoped Classical Topology

namespace LovaszTheta.Independent

private lemma expectedTheta_bound_good {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B)
    (good : SignSample n → Prop)
    (hGood : ∀ x, good x → theta (graph x) ≤ 1+B*Real.sqrt n) :
    expectedTheta n / Real.sqrt n ≤ 1/Real.sqrt n+B+
      Real.sqrt n*probability (fun x ↦ ¬good x) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hsq : s*s = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hp (x : SignSample n) : theta (graph x)/s ≤ 1/s+B+s*(if ¬good x then 1 else 0) := by
    by_cases hx : good x
    · rw [ite_eq_right (not_not.mpr hx),mul_zero,add_zero]
      exact (div_le_iff₀ hs).mpr (by rw [add_mul,div_mul_cancel₀ 1 hs.ne']; exact hGood x hx)
    · rw [ite_eq_left hx,mul_one]
      have hTheta : theta (graph x)/s ≤ s := by
        apply (div_le_iff₀ hs).mpr
        rw [hsq]
        have h := theta_le_card (graph x)
        simpa only [Fintype.card_fin] using h
      exact hTheta.trans (le_add_of_nonneg_left (add_nonneg (div_nonneg zero_le_one hs.le) hB))
  have h := average_mono hp
  have hm : average (fun x : SignSample n ↦ theta (graph x)/s) = expectedTheta n/s := by
    simp only [div_eq_inv_mul,average_mul_left,expectedTheta]
  have hProb : (average fun x : SignSample n ↦ if ¬good x then (1 : ℝ) else 0) =
      probability (fun x : SignSample n ↦ ¬good x) := by
    unfold probability
    apply congrArg (average (Ω := SignSample n))
    funext x
    by_cases hx : good x <;> simp [hx]
  rw [hm,average_add,average_const,average_mul_left,hProb] at h
  exact h

private lemma eventually_expectedTheta_upper (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, expectedTheta n/Real.sqrt n ≤
      (bernsteinCoefficient N 0+η)/singleEdgeCoefficient N+1/Real.sqrt n+(n : ℝ)⁻¹ := by
  let B := (bernsteinCoefficient N 0+η)/singleEdgeCoefficient N
  have hB : 0 ≤ B := div_nonneg (add_nonneg (bernsteinCoefficient_zero_pos hN).le hη.le)
    (singleEdgeCoefficient_pos hN).le
  have hEvent := withHighProbability_theta_le N hN hη (bernsteinCoefficient_zero_pos hN).le
  filter_upwards [hEvent 2 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hP hn
  have hPos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS : Real.sqrt (n : ℝ) ≤ n := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hPos.le
    rw [Real.sq_sqrt hPos.le,pow_two]
    exact le_mul_of_one_le_right hPos.le hnR
  have hTail : Real.sqrt (n : ℝ)*(n : ℝ)^(-2 : ℝ) ≤ (n : ℝ)⁻¹ := by
    refine (mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hPos.le _)).trans_eq ?_
    calc
      _ = (n : ℝ)^(1 : ℝ)*(n : ℝ)^(-2 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hPos,show (1 : ℝ)+(-2) = -1 by norm_num,Real.rpow_neg_one]
  let good (x : SignSample n) := theta (graph x) ≤ 1+B*Real.sqrt n
  have h := expectedTheta_bound_good (show 0 < n by omega) hB good (fun _ hx ↦ hx)
  have hP' : probability (fun x ↦ ¬good x) ≤ (n : ℝ)^(-2 : ℝ) := hP
  have hMul := mul_le_mul_of_nonneg_left hP' (Real.sqrt_nonneg (n : ℝ))
  change expectedTheta n/Real.sqrt n ≤ B+1/Real.sqrt n+(n : ℝ)⁻¹
  linarith only [h,hMul,hTail]

private lemma eventually_expectedTheta_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, expectedTheta n/Real.sqrt n ≤ 1+ε := by
  have hRatio : Tendsto (fun m : ℕ ↦ bernsteinCoefficient (m+2) 0/singleEdgeCoefficient (m+2))
      atTop (𝓝 1) := by
    have h := tendsto_singleEdgeCoefficient_div_bernsteinCoefficient.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)
    simpa only [inv_div,inv_one] using h
  obtain ⟨m,hm⟩ := (hRatio.eventually_le_const (show (1 : ℝ) < 1+ε/3 by linarith)).exists
  let N := m+2
  have hN : 0 < N := by unfold N; omega
  let η := singleEdgeCoefficient N*ε/3
  have hη : 0 < η := by unfold η; exact div_pos (mul_pos (singleEdgeCoefficient_pos hN) hε) (by norm_num)
  have hB : (bernsteinCoefficient N 0+η)/singleEdgeCoefficient N ≤ 1+2*ε/3 := by
    rw [add_div]
    have he : η/singleEdgeCoefficient N = ε/3 := by
      unfold η
      field_simp [(singleEdgeCoefficient_pos hN).ne']
    rw [he]
    change bernsteinCoefficient N 0/singleEdgeCoefficient N ≤ 1+ε/3 at hm
    linarith
  have hInv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hSqrt : Tendsto (fun n : ℕ ↦ 1/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hTail : Tendsto (fun n : ℕ ↦ 1/Real.sqrt (n : ℝ)+(n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [add_zero] using hSqrt.add hInv
  filter_upwards [eventually_expectedTheta_upper N hN hη, hTail.eventually_le_const
    (show (0 : ℝ) < ε/3 by positivity)] with n h₁ h₂
  linarith

/-- The normalized expected Lovász theta of the independent-edge graph tends to one. -/
theorem tendsto_normalizedExpectedTheta :
    Tendsto (fun m : ℕ ↦ expectedTheta (m+1)/Real.sqrt (m+1 : ℕ)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_add_atTop_nat 1).eventually
    (eventually_expectedTheta_close (show (0 : ℝ) < ε/2 by positivity))
  filter_upwards [he] with m hm
  have hn : 0 < m+1 := Nat.zero_lt_succ _
  let : NeZero (m+1) := ⟨hn.ne'⟩
  have hs : 0 < Real.sqrt ((m+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hLower : 1 ≤ expectedTheta (m+1)/Real.sqrt (m+1 : ℕ) := by
    rw [le_div_iff₀ hs,one_mul]
    exact sqrt_le_expectedTheta (m+1)
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hLower)]
  change expectedTheta (m+1)/Real.sqrt (m+1 : ℕ) ≤ 1+ε/2 at hm
  linarith

end LovaszTheta.Independent
