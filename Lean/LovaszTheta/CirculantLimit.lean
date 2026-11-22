module

public import LovaszTheta.TrialApproximation

/-!
# The expectation limit for random circulants

Use the finite trial estimate with the logarithmic cutoff and the
discrepancy threshold (1/log n). The Fourier tail gives a negligible
contribution from the failed events. Finally send the smoothing
parameter to zero and apply the complement lower bound.
-/

@[expose] public section

open Filter Set
open scoped Topology Classical

namespace LovaszTheta.Circulant

/-- Normalized circulant theta expectation over the positive orders. -/
noncomputable def normalizedExpectedTheta (m : ℕ) : ℝ :=
  expectedTheta (m+1) / Real.sqrt (m+1 : ℕ)

private lemma tendsto_log_succ_atTop : Tendsto (fun m : ℕ ↦ Real.log ((m+1 : ℕ) : ℝ)) atTop atTop :=
  tendsto_log_nat_atTop.comp (tendsto_add_atTop_nat 1)

private lemma eventually_normalizedExpectedTheta_lt_of_smoothing {τ : ℝ} (hτ : 0 < τ)
    {b : ℝ} (hb : Real.sqrt (1+τ) < b) :
    ∀ᶠ m : ℕ in atTop, normalizedExpectedTheta m < b := by
  obtain ⟨σ,hσ,_,hVariance,hMean⟩ := exists_gaussian_activation_scale hτ
  have hσ' : σ ≤ Real.sqrt (2*Real.pi) := (Real.le_sqrt hσ.le (by positivity)).mpr hVariance
  let A := EvenTreeType.trialSequenceEnergy hτ hσ hσ' hMean
  let B := EvenTreeType.trialSequenceResidual hτ hσ hσ' hMean
  let C := EvenTreeType.trialSequenceOrigin hτ hσ hσ' hMean
  let L (m : ℕ) := Real.log ((m+1 : ℕ) : ℝ)
  let δ (m : ℕ) := (Real.sqrt (L m))⁻¹
  let K := Real.sqrt (4*Real.pi)+262144*Real.sqrt (1+τ)
  let u (m : ℕ) := Real.sqrt (1+τ)*Real.exp (3*δ m/2)
  let e (m : ℕ) := 5*(4*(L m*Real.exp (-L m)) + (L m)^2*C m + K*((L m)^6*Real.sqrt (B m))) +
    2*((m+1 : ℕ) : ℝ)⁻¹^2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    apply ((tendsto_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num)).comp tendsto_log_succ_atTop).inv_tendsto_atTop.congr'
    exact Eventually.of_forall fun m ↦ by
      change (L m ^ (1/2 : ℝ))⁻¹ = (Real.sqrt (L m))⁻¹
      rw [Real.sqrt_eq_rpow]
  have hU : Tendsto u atTop (𝓝 (Real.sqrt (1+τ))) := by
    have h := ((hδ.const_mul 3).div_const 2).rexp.const_mul (Real.sqrt (1+τ))
    simpa only [mul_zero,zero_div,Real.exp_zero,mul_one] using h
  have hLexp : Tendsto (fun m ↦ L m*Real.exp (-L m)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one).comp tendsto_log_succ_atTop
    change Tendsto (fun m ↦ L m^(1 : ℝ)*Real.exp ((-1 : ℝ)*L m)) atTop (𝓝 0) at h
    simpa only [Real.rpow_one,neg_one_mul] using h
  have hC := EvenTreeType.tendsto_log_sq_trialSequenceOrigin hτ hσ hσ' hMean
  have hB : Tendsto (fun m ↦ (L m)^6*Real.sqrt (B m)) atTop (𝓝 0) := by
    have h := (EvenTreeType.tendsto_log_pow_trialSequenceResidual hτ hσ hσ' hMean).sqrt
    rw [Real.sqrt_zero] at h
    refine h.congr' ?_
    filter_upwards [tendsto_log_succ_atTop.eventually_ge_atTop 1] with m hm
    have h₀ : 0 ≤ L m := zero_le_one.trans hm
    change Real.sqrt ((L m)^12*B m) = _
    rw [Real.sqrt_mul (pow_nonneg h₀ _),show (L m)^12 = ((L m)^6)^2 by rw [← pow_mul],
      Real.sqrt_sq (pow_nonneg h₀ _)]
  have hInv : Tendsto (fun m : ℕ ↦ (((m+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  have hE : Tendsto e atTop (𝓝 0) := by
    have h := ((((hLexp.const_mul 4).add hC).add (hB.const_mul K)).const_mul 5).add ((hInv.pow 2).const_mul 2)
    simpa only [mul_zero,add_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  have hSum : Tendsto (fun m ↦ u m + e m) atTop (𝓝 (Real.sqrt (1+τ))) := by
    simpa only [add_zero] using hU.add hE
  filter_upwards [hSum.eventually (Iio_mem_nhds hb),EvenTreeType.eventually_trialSequenceEnergy_le hτ hσ hσ' hMean,
    eventually_ge_atTop (1 : ℕ),tendsto_log_succ_atTop.eventually_ge_atTop (max 1 (Real.log 8))]
    with m hLim hA hm hL
  let N := m+1
  let l := L m
  let r := kernelLog N
  let w := (1+4*Real.sqrt ((N : ℝ)*l))/Real.sqrt N
  have hn : 1 < N := by unfold N; omega
  have hN : 0 < (N : ℝ) := by positivity
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hn.le
  have hl : 1 ≤ l := (le_max_left _ _).trans hL
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  have hδp : 0 < δ m := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hl))
  have hδsq : (δ m)^2 = l⁻¹ := by unfold δ; rw [inv_pow,Real.sq_sqrt hl0]
  have hlog : r = Real.log 8+l := by unfold r kernelLog; rw [Real.log_mul (by norm_num) hN.ne']
  have hRlow : l ≤ r := by rw [hlog]; exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
  have hRup : r ≤ 2*l := by
    have h₈ : Real.log 8 ≤ l := (le_max_right _ _).trans hL
    rw [hlog]
    linarith only [h₈]
  have hW : w ≤ 5*l := by
    unfold w
    rw [add_div,Real.sqrt_mul hN.le,mul_left_comm 4, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hN).ne']
    have hInvNp : 1/Real.sqrt (N : ℝ) ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hN)).mpr (Real.one_le_sqrt.mpr hN1)
    linarith only [hInvNp,sqrt_le_self_of_one_le hl,hl]
  have hW₀ : 0 ≤ w := by unfold w; positivity
  have hK : 0 ≤ K := by unfold K; positivity
  have hR : 4*Real.exp (-(r^2)) ≤ 4*Real.exp (-l) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by norm_num)
    exact (le_self_pow₀ hl (by decide : (2 : ℕ) ≠ 0)).trans (pow_le_pow_left₀ hl0 hRlow 2)
  have hR2 : r^2 ≤ 4*l^2 := (pow_le_pow_left₀ (hl0.trans hRlow) hRup 2).trans_eq (by ring)
  have hRes : Real.sqrt (A m)+65536*Real.sqrt (1+τ)*r^2 ≤ K*l^2 := by
    have hSq : (1 : ℝ) ≤ l^2 := one_le_pow₀ hl
    calc
      _ ≤ Real.sqrt (4*Real.pi)+65536*Real.sqrt (1+τ)*(4*l^2) :=
        add_le_add (Real.sqrt_le_sqrt hA) (mul_le_mul_of_nonneg_left hR2 (by positivity))
      _ ≤ Real.sqrt (4*Real.pi)*l^2+65536*Real.sqrt (1+τ)*(4*l^2) :=
        add_le_add_left (le_mul_of_one_le_right (Real.sqrt_nonneg _) hSq) _
      _ = _ := by unfold K; ring
  have hB0 : 0 ≤ B m := average_sq_nonneg _
  have hC0 : 0 ≤ C m := average_sq_nonneg _
  have hNon : 0 ≤ 4*Real.exp (-(r^2)) + C m/(δ m)^2 +
      (Real.sqrt (A m)+65536*Real.sqrt (1+τ)*r^2)*Real.sqrt (B m)/(δ m)^2 := by positivity
  have hErr :
      w*(4*Real.exp (-(r^2)) + C m/(δ m)^2 +
        (Real.sqrt (A m)+65536*Real.sqrt (1+τ)*r^2)*Real.sqrt (B m)/(δ m)^2) ≤
      5*(4*(l*Real.exp (-l)) + l^2*C m + K*(l^6*Real.sqrt (B m))) := by
    rw [hδsq,div_inv_eq_mul,div_inv_eq_mul] at hNon ⊢
    calc
      _ ≤ (5*l)*(4*Real.exp (-l)+C m*l+(K*l^2)*Real.sqrt (B m)*l) :=
        mul_le_mul hW (add_le_add (add_le_add_left hR _)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRes (Real.sqrt_nonneg _)) hl0)) hNon (by positivity)
      _ = 5*(4*(l*Real.exp (-l))+l^2*C m+K*(l^4*Real.sqrt (B m))) := by ring
      _ ≤ _ := by
        have hp : l^4 ≤ l^6 := pow_right_mono₀ hl (by decide)
        gcongr
  have hSpectral : Real.sqrt (N : ℝ)*(2*(N : ℝ)⁻¹^3) ≤ 2*(N : ℝ)⁻¹^2 := by
    refine (mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le hN1) (by positivity)).trans_eq ?_
    field_simp [hN.ne']
  have h : normalizedExpectedTheta m ≤ u m +
      w*(4*Real.exp (-(r^2)) + C m/(δ m)^2 +
        (Real.sqrt (A m)+65536*Real.sqrt (1+τ)*r^2)*Real.sqrt (B m)/(δ m)^2) +
      Real.sqrt (N : ℝ)*(2*(N : ℝ)⁻¹^3) :=
    expectedTheta_div_sqrt_le_of_trial (n := N) hn hτ hδp (EvenTreeType.trialSequence hτ hσ hσ' hMean m)
  have hUpper : normalizedExpectedTheta m ≤ u m+e m :=
    h.trans ((add_le_add (add_le_add_right hErr (u m)) hSpectral).trans_eq (add_assoc (u m) _ _))
  exact hUpper.trans_lt hLim

/-- The random circulant theta expectation is asymptotic to √n over all positive orders. -/
theorem tendsto_normalizedExpectedTheta : Tendsto normalizedExpectedTheta atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun m ↦ ha.trans_le (by
      unfold normalizedExpectedTheta
      exact (le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr
        (by simpa only [one_mul] using sqrt_le_expectedTheta (m+1)))
  · intro b hb
    let τ := (b-1)/2
    have hτ : 0 < τ := by unfold τ; linarith
    have hU : Real.sqrt (1+τ) < b :=
      (sqrt_le_self_of_one_le (by linarith : (1 : ℝ) ≤ 1+τ)).trans_lt (by unfold τ; linarith)
    exact eventually_normalizedExpectedTheta_lt_of_smoothing hτ hU

end LovaszTheta.Circulant
