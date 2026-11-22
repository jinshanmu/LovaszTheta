module

public import LovaszTheta.TrialEnvelopes
public import LovaszTheta.TrialCutoff

/-!
# The trial approximation at growing order

The finite bounds at the common logarithmic cutoff give a bounded
trial norm, a negligible zero coordinate, and residual mean square
that tends to zero after multiplication by log to the twelfth power.
-/

@[expose] public section

open Filter
open scoped Topology Classical

namespace LovaszTheta.Circulant

theorem CutoffEnvelope.tendsto_log_pow_div_sqrt {f : ℕ → ℝ} (hf : CutoffEnvelope f) (r : ℕ) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))^r * (f (trialCutoff n)/Real.sqrt n)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hf⟩ := hf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_log_pow_cutoff_exp_div_sqrt r hC)
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hn) _) (div_nonneg (hf _).1 (by positivity))
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hf _).2 (by positivity))
      (pow_nonneg (zero_le_one.trans hn) _)

lemma CutoffEnvelope.nonneg {f : ℕ → ℝ} (hf : CutoffEnvelope f) (D : ℕ) : 0 ≤ f D :=
  (hf.choose_spec.2 D).1

namespace EvenTreeType

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))

local notation "logOrder" n => Real.log ((n+1 : ℕ) : ℝ)
local notation "cutoff" n => trialCutoff (n+1)

/-- The trial vectors over all positive orders, indexed by order minus one. -/
noncomputable def trialSequence (n : ℕ) : (InversionClass (n+1) → Bool) → ZMod (n+1) → ℝ :=
  trialVector hτ hσ hσ' hMean (cutoff n)

/-- The mean square of the trial vector. -/
noncomputable def trialSequenceEnergy (n : ℕ) : ℝ :=
  average fun x ↦ norm₂ (trialSequence hτ hσ hσ' hMean n x)^2

/-- The mean square of the trial residual. -/
noncomputable def trialSequenceResidual (n : ℕ) : ℝ :=
  average fun x ↦
    norm₂ (trialSequence hτ hσ hσ' hMean n x -
      signOperator x (smooth (weight (n+1) τ) (trialSequence hτ hσ hσ' hMean n x)))^2

/-- The mean square at the distinguished Fourier coordinate. -/
noncomputable def trialSequenceOrigin (n : ℕ) : ℝ :=
  average fun x ↦ (trialSequence hτ hσ hσ' hMean n x 0)^2

lemma eventually_trialSequenceEnergy_le :
    ∀ᶠ n : ℕ in atTop, trialSequenceEnergy hτ hσ hσ' hMean n ≤ 4*Real.pi := by
  have h1 := (tendsto_trialCutoff_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 1
  have h := (CutoffEnvelope.linearTransfer_size.tendsto_log_pow_div_sqrt 0).comp (tendsto_add_atTop_nat 1)
  simp only [pow_zero,one_mul] at h
  filter_upwards [h1,h.eventually (Iio_mem_nhds zero_lt_one)] with n hD he
  have hTr := average_norm_sq_trialVector_le hτ hσ hσ' hMean (n := n+1) hD
  have hl : linearTransferError (cutoff n) (n+1) ≤ 1 :=
    (linearTransferError_le _ _).trans he.le
  have hP : (2*Real.pi)*(1+linearTransferError (cutoff n) (n+1)) ≤ (2*Real.pi)*2 :=
    mul_le_mul_of_nonneg_left (by linarith only [hl]) (by positivity)
  exact hTr.trans (hP.trans_eq (by ring))

theorem tendsto_log_sq_trialSequenceOrigin :
    Tendsto (fun n : ℕ ↦ (logOrder n)^2 * trialSequenceOrigin hτ hσ hσ' hMean n) atTop (𝓝 0) := by
  have h := (CutoffEnvelope.linearTransfer_zero.tendsto_log_pow_div_sqrt 2).comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Eventually.of_forall (fun n ↦ mul_nonneg (sq_nonneg _) (average_sq_nonneg _))
  · filter_upwards [(tendsto_trialCutoff_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 1]
      with n hD
    have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
    have hp : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (average_sq_trialVector_zero_le hτ hσ hσ' hMean (n := n+1) hD).trans
      (div_le_div_of_nonneg_left (CutoffEnvelope.linearTransfer_zero.nonneg (cutoff n))
        hp (sqrt_le_self_of_one_le hn))

theorem tendsto_log_pow_trialSequenceResidual :
    Tendsto (fun n : ℕ ↦ (logOrder n)^12 * trialSequenceResidual hτ hσ hσ' hMean n) atTop (𝓝 0) := by
  obtain ⟨K,hK,hAct⟩ := exists_activation_derivatives_le hτ
  obtain ⟨C,hC,hTail⟩ := activationCoefficient_sq_tail_le (p := 200) hτ (by decide)
  let W := σ^2*(∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^200)
  let V := 4*(12*W+7*C)
  let f (D : ℕ) := 4*(graftingTransferScale τ D D + activationTransferScale τ K D D +
    8*((2*Real.pi)*((4 : ℝ)^D*treeMomentEnvelope D)+τ))
  have hf : CutoffEnvelope f :=
    (CutoffEnvelope.const (by norm_num : (0 : ℝ) ≤ 4)).mul
      (((CutoffEnvelope.grafting hτ.le).add (CutoffEnvelope.activation hK)).add
        ((CutoffEnvelope.const (by norm_num : (0 : ℝ) ≤ 8)).mul
          (CutoffEnvelope.linearTransfer_zero.add (CutoffEnvelope.const hτ.le))))
  have hFinal := ((tendsto_log_pow_div_trialCutoff_pow.const_mul V).add
    (hf.tendsto_log_pow_div_sqrt 12)).comp (tendsto_add_atTop_nat 1)
  simp only [mul_zero,zero_add] at hFinal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hFinal
  · filter_upwards [tendsto_log_nat_atTop.comp (tendsto_add_atTop_nat 1) |>.eventually_ge_atTop 1] with n hL
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) (average_sq_nonneg _)
  · have hb := (CutoffEnvelope.linearTransfer_graft.tendsto_log_pow_div_sqrt 0).comp (tendsto_add_atTop_nat 1)
    simp only [pow_zero,one_mul] at hb
    filter_upwards [(tendsto_trialCutoff_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 400,
      hb.eventually (Iio_mem_nhds zero_lt_one),eventually_ge_atTop (1 : ℕ),
      (tendsto_log_nat_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 1] with n hD he hn hL
    let N := n+1
    let D := trialCutoff N
    let s := gaussianSizeScale hτ hσ hσ' hMean D
    let t := ∑' j : ℕ, activationCoefficient τ s (j+(D+1))^2
    let e := linearTransferError (1+D*D) N
    have hn' : 1 < N := by unfold N; omega
    let _ : Nonempty (InversionClass N) :=
      ⟨inversionClass 1 (fun he ↦ hn'.ne' (ZMod.one_eq_zero_iff.mp he))⟩
    have hD' : 0 < D := lt_of_lt_of_le (by decide : 0 < 400) hD
    have hS := gaussianSizeScale_bounds hτ hσ hσ' hMean hD'
    have ht : t ≤ C/(D : ℝ)^200 := hTail s (by linarith only [hS.1]) hS.2 D (by exact hD)
    have hB := average_trialVector_residual_sq_le hτ hσ hσ' hMean (n := N) hD' hD' 200 hK hAct
    have hE : 1+e ≤ 2 := by
      have hh : e ≤ 1 := (linearTransferError_le _ _).trans he.le
      linarith only [hh]
    have hT0 : 0 ≤ t := tsum_nonneg fun _ ↦ sq_nonneg _
    have hW : 0 ≤ W := mul_nonneg (sq_nonneg _) (tsum_nonneg fun _ ↦ by positivity)
    have hFirst : (6*(W/(D : ℝ)^200)+3*t)*(1+e)+t ≤ (12*W+7*C)/(D : ℝ)^200 := by
      have hP : 0 ≤ 6*(W/(D : ℝ)^200)+3*t :=
        add_nonneg (mul_nonneg (by norm_num) (div_nonneg hW (by positivity))) (mul_nonneg (by norm_num) hT0)
      have hh := mul_le_mul_of_nonneg_left hE hP
      calc
        _ ≤ (6*(W/(D : ℝ)^200)+3*t)*2+t := add_le_add_left hh _
        _ ≤ 12*(W/(D : ℝ)^200)+7*(C/(D : ℝ)^200) := by linarith only [ht]
        _ = _ := by ring
    let z := (2*Real.pi)*((4 : ℝ)^D*treeMomentEnvelope D)
    have hZ : 0 ≤ z+τ := add_nonneg (CutoffEnvelope.linearTransfer_zero.nonneg D) hτ.le
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn'.le
    have hN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hSecond : z/N+τ/N ≤ (z+τ)/Real.sqrt N := by
      rw [← add_div]
      exact div_le_div_of_nonneg_left hZ hN (sqrt_le_self_of_one_le hN1)
    have hBound : trialSequenceResidual hτ hσ hσ' hMean n ≤ V/(D : ℝ)^200+f D/Real.sqrt N := by
      refine hB.trans ?_
      change 4*((6*(W/(D : ℝ)^200)+3*t)*(1+e)+graftingTransferScale τ D D/Real.sqrt N +
        (t+activationTransferScale τ K D D/Real.sqrt N)+8*(z/N+τ/N)) ≤ _
      dsimp only [V,f,z] at *
      linear_combination (norm := ring_nf) 4*hFirst + 32*hSecond
      exact le_rfl
    refine (mul_le_mul_of_nonneg_left hBound (pow_nonneg (zero_le_one.trans hL) _)).trans_eq ?_
    change (Real.log (N : ℝ))^12 * (V/(D : ℝ)^200+f D/Real.sqrt N) =
      V*((Real.log (N : ℝ))^12/(D : ℝ)^200)+(Real.log (N : ℝ))^12*(f D/Real.sqrt N)
    ring

end EvenTreeType

end LovaszTheta.Circulant
