module

public import LovaszTheta.TrialVector

/-!
# Quantitative bounds for the smoothed trial residual

The approximation terms separate into the Gaussian size and
degree tails, and finite-order errors with explicit envelopes.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

lemma sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h₀ := zero_le_one.trans hx
  apply (Real.sqrt_le_left h₀).mpr
  rw [pow_two]
  exact le_mul_of_one_le_right h₀ hx

private lemma inverse_modulus_le_inverse_sqrt (n : ℕ) [NeZero n] :
    (n : ℝ)⁻¹ ≤ (Real.sqrt n)⁻¹ := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  exact inv_anti₀ h' (sqrt_le_self_of_one_le h)

private lemma div_modulus_le_div_sqrt (n : ℕ) [NeZero n] {a : ℝ} (ha : 0 ≤ a) :
    a/(n : ℝ) ≤ a/Real.sqrt n := by
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inverse_modulus_le_inverse_sqrt n) ha

/-- A bound on the relative linear transfer error before division by √n. -/
noncomputable def linearTransferScale (D : ℕ) : ℝ :=
  (4 : ℝ)^D*(3*treeMomentEnvelope D+2)

lemma linearTransferError_le (D n : ℕ) [NeZero n] :
    EvenTreeType.linearTransferError D n ≤ linearTransferScale D / Real.sqrt n := by
  unfold EvenTreeType.linearTransferError linearTransferScale
  have h := div_modulus_le_div_sqrt n (a := 2) (by norm_num)
  have hB : 0 ≤ treeMomentEnvelope D + 1 := by unfold treeMomentEnvelope; positivity
  calc
    _ ≤ 4^D*(treeMomentEnvelope D / Real.sqrt n + (treeMomentEnvelope D+1)*(2/Real.sqrt n)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left h hB) _) (by positivity)
    _ = _ := by ring

/-- The finite activation-test envelope for the spatial error. -/
noncomputable def activationTransferScale (τ K : ℝ) (D M : ℕ) : ℝ :=
  let r : ℝ := 2*(M : ℝ)+3
  let u : ℝ := 2*Real.pi+4*(D : ℝ)
  (8*(Real.sqrt (2*Real.pi+4*τ)*(M+1 : ℝ)^4*(M.factorial : ℝ)+K)^2) *
    (comparisonEnvelope (2*Real.pi) D M +
      2*Real.exp (6*r+3+r*(2*r*D+2*u+28*(D : ℝ)^2)))

/-- The envelope of the finite grafting error. -/
noncomputable def graftingTransferScale (τ : ℝ) (D M : ℕ) : ℝ :=
  (2*Real.pi+4*τ)*((4 : ℝ)^D+1)^M *
    (10*EvenTreeType.graftProductErrorScale D M+3*treeMomentEnvelope (1+D*M)+4)

namespace EvenTreeType

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) {n : ℕ} [NeZero n]

local notation "scale" => gaussianSizeScale hτ hσ hσ' hMean
local notation "direction" => gaussianSizeDirection hτ hσ hσ' hMean
local notation "H" => trialField hτ hσ hσ' hMean

omit [NeZero n] in
private lemma sum_abs_trialCoefficients_le {D : ℕ} (hD : 0 < D) :
    (∑ i ∈ typesThroughSize D, |trialCoefficients hτ hσ hσ' hMean D i|) ≤ (2*Real.pi)*4^D := by
  let a := trialCoefficients hτ hσ hσ' hMean D
  let v := scale D
  have hV := gaussianSizeScale_bounds hτ hσ hσ' hMean hD
  have hv : 0 ≤ v := by linarith only [hV.1]
  have hA : (∑ i ∈ typesThroughSize D, a i ^ 2) = v^2 := by
    rw [sum_sq_eq_gaussianCoefficient_norm_sq (trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D),
      norm_trialCoefficients hτ hσ hσ' hMean hD]
  have hπ : 1 ≤ 2*Real.pi := by
    have h := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (hV.1.trans hV.2) 2).trans_eq (Real.sq_sqrt (by positivity))
    linarith only [h]
  have hvb : v ≤ 2*Real.pi := hV.2.trans (sqrt_le_self_of_one_le hπ)
  calc
    _ ≤ ∑ i ∈ typesThroughSize D, v := by
      apply sum_le_sum
      intro i hi
      have ho : a i^2 ≤ v^2 := (single_le_sum (fun j _ ↦ sq_nonneg (a j)) hi).trans_eq hA
      simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg hv] using Real.sqrt_le_sqrt ho
    _ = ((typesThroughSize D).card : ℝ)*v := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hC : ((typesThroughSize D).card : ℝ) ≤ (4 : ℝ)^D := by exact_mod_cast card_typesThroughSize_le D
      exact (mul_le_mul hC hvb hv (by positivity)).trans_eq (mul_comm _ _)

private lemma exponential_trial_coefficients {D : ℕ} (hD : 0 < D) :
    (∑ i ∈ typesThroughSize D, |trialCoefficients hτ hσ hσ' hMean D i|) ≤
      Real.exp (2*Real.pi+4*(D : ℝ)) := by
  have h₄ : (4 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp 4]
  have hp : 2*Real.pi ≤ Real.exp (2*Real.pi) := by linarith only [Real.add_one_le_exp (2*Real.pi)]
  rw [Real.exp_add,show 4*(D : ℝ) = (D : ℝ)*4 by ring,Real.exp_nat_mul]
  exact (sum_abs_trialCoefficients_le hτ hσ hσ' hMean hD).trans
    (mul_le_mul hp (pow_le_pow_left₀ (by norm_num) h₄ D) (by positivity) (Real.exp_nonneg _))

theorem average_spatial_trialField_activation_le [Nonempty (InversionClass n)]
    {D : ℕ} (hD : 0 < D) (M : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hAct : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j (activation τ) x| ≤ K*(1+|x|)) :
    average (fun k : ZMod n ↦ average (fun x ↦
      (activationProjection τ (scale D) M (H D x k) - activation τ (H D x k))^2)) ≤
      (∑' j : ℕ, activationCoefficient τ (scale D) (j+(M+1))^2) +
        activationTransferScale τ K D M/Real.sqrt n := by
  let s := typesThroughSize D
  let a := trialCoefficients hτ hσ hσ' hMean D
  let v := scale D
  have hVB := gaussianSizeScale_bounds hτ hσ hσ' hMean hD
  have hVar : v^2 ≤ 2*Real.pi := (pow_le_pow_left₀ (by linarith only [hVB.1]) hVB.2 2).trans_eq
    (Real.sq_sqrt (by positivity))
  have hA : (∑ i : s, a i.val ^ 2) = v^2 := by
    rw [sum_coe_sort s (fun i ↦ (a i)^2),
      sum_sq_eq_gaussianCoefficient_norm_sq (trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D),
      norm_trialCoefficients hτ hσ hσ' hMean hD]
  simp_rw [trialField,evaluateCoefficients_eq_treeLinearEvaluation]
  have hAbs : (∑ i : s, |a i.val|) ≤ (2*Real.pi)*4^D := by
    rw [sum_coe_sort s (fun i ↦ |a i|)]
    exact sum_abs_trialCoefficients_le hτ hσ hσ' hMean hD
  refine (average_spatial_activationProjection_sub_sq_le (fun i : s ↦ a i.val)
    (fun T ↦ T.val.representative) D M
    (fun T ↦ (representative_nodeCount _).trans_le ((mem_typesThroughSize _ _).mp T.property))
    (fun T U e ↦ Subtype.ext ((representative_isomorphism_iff U.val T.val).mp e).symm)
    hτ (by linarith only [hVB.1]) hA.symm (by positivity) hAbs hVar hK hAct).trans ?_
  dsimp only
  apply add_le_add_right
  have hX := comparisonSignGrowth_le_exp D (2*M+3) (∑ i : s, |a i.val|) (2*Real.pi+4*(D : ℝ))
    (sum_nonneg fun _ _ ↦ abs_nonneg _) (by positivity)
    ((sum_coe_sort s (fun i ↦ |a i|)).trans_le (exponential_trial_coefficients hτ hσ hσ' hMean hD))
  have hr : ((2*M+3 : ℕ) : ℝ) = 2*(M : ℝ)+3 := by push_cast; rfl
  rw [hr] at hX
  have hCoeff : Real.sqrt (v^2+4*τ)*(M+1 : ℝ)^4*(M.factorial : ℝ)+K ≤
      Real.sqrt (2*Real.pi+4*τ)*(M+1 : ℝ)^4*(M.factorial : ℝ)+K :=
    add_le_add_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (add_le_add_left hVar _)) (by positivity)) (by positivity)) _
  have hCoeff₀ : 0 ≤ Real.sqrt (v^2+4*τ)*(M+1 : ℝ)^4*(M.factorial : ℝ)+K := by positivity
  unfold activationTransferScale
  refine (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCoeff₀ hCoeff 2) (by norm_num))
    (add_le_add_right (mul_le_mul hX (div_modulus_le_div_sqrt n (a := 2) (by norm_num))
      (by positivity) (Real.exp_nonneg _)) _) (by unfold comparisonEnvelope comparisonSignGrowth; positivity)
    (by positivity)).trans_eq ?_
  ring

theorem average_spatial_trialField_grafting_le [Nonempty (InversionClass n)]
    {D : ℕ} (hD : 0 < D) (M : ℕ) :
    average (fun k : ZMod n ↦ average (fun x ↦
      (signOperator x (fun j ↦ activationProjection τ (scale D) M (H D x j)) k -
        graftedActivationField (typesThroughSize D) M τ (scale D) (direction D) x k)^2)) ≤
      graftingTransferScale τ D M / Real.sqrt n := by
  have hV := gaussianSizeScale_bounds hτ hσ hσ' hMean hD
  have hPos : 0 < scale D := zero_lt_two.trans_le hV.1
  simp_rw [trialField_eq_sum]
  refine (average_spatial_sq_graftedActivationField_le (typesThroughSize D) D M
    (fun i hi ↦ (mem_typesThroughSize _ _).mp hi) hτ.le hPos.ne' (direction D)
    (by rw [sum_sq_eq_gaussianCoefficient_norm_sq (gaussianSizeDirection_apply_of_notMem hτ hσ hσ' hMean D),
      norm_gaussianSizeDirection hτ hσ hσ' hMean hD,one_pow])).trans ?_
  have hVar : (scale D)^2 ≤ 2*Real.pi :=
    (pow_le_pow_left₀ hPos.le hV.2 2).trans_eq (Real.sq_sqrt (by positivity))
  have hC : ((typesThroughSize D).card : ℝ) ≤ (4 : ℝ)^D := by exact_mod_cast card_typesThroughSize_le D
  have hR : 0 ≤ graftResidualError D M n := by
    unfold graftResidualError graftProductErrorScale comparisonEnvelope treeMomentEnvelope
    positivity
  have hQ : 0 ≤ graftProductErrorScale D M := by unfold graftProductErrorScale comparisonEnvelope; positivity
  have hG : 0 ≤ treeMomentEnvelope (1+D*M)+2 := by unfold treeMomentEnvelope; positivity
  have hR' : graftResidualError D M n ≤
      (10*graftProductErrorScale D M+3*treeMomentEnvelope (1+D*M)+4)/Real.sqrt n := by
    unfold graftResidualError
    refine (add_le_add
      (add_le_add_left (mul_le_mul_of_nonneg_left
        (add_le_add_right (div_modulus_le_div_sqrt n (a := 8) (by norm_num)) _) hQ) _)
      (mul_le_mul_of_nonneg_left (div_modulus_le_div_sqrt n (a := 2) (by norm_num)) hG)).trans_eq ?_
    ring
  unfold graftingTransferScale
  refine (mul_le_mul (mul_le_mul (add_le_add_left hVar _)
    (pow_le_pow_left₀ (by positivity) (add_le_add_left hC _) M) (by positivity) (by positivity))
    hR' hR (by positivity)).trans_eq ?_
  ring

/-- Finite estimate for the trial residual, with the two Gaussian
tails and the explicit finite-order errors. -/
theorem average_trialVector_residual_sq_le [Nonempty (InversionClass n)]
    {D M : ℕ} (hD : 0 < D) (hM : 0 < M) (p : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hAct : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j (activation τ) x| ≤ K*(1+|x|)) :
    let v := trialVector hτ hσ hσ' hMean D
    let t := ∑' j : ℕ, activationCoefficient τ (scale D) (j+(M+1))^2
    let b := σ^2 * (∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) / (D : ℝ)^p
    average (fun x : InversionClass n → Bool ↦
      norm₂ (v x - signOperator x (smooth (weight n τ) (v x)))^2) ≤
      4*((6*b+3*t)*(1+linearTransferError (1+D*M) n) +
        graftingTransferScale τ D M / Real.sqrt n +
        (t+activationTransferScale τ K D M / Real.sqrt n) +
        8*((2*Real.pi)*((4 : ℝ)^D*treeMomentEnvelope D)/(n : ℝ)+τ/n)) := by
  let v := trialVector (n := n) hτ hσ hσ' hMean D
  let P (x : InversionClass n → Bool) (k : ZMod n) := activationProjection τ (scale D) M (H D x k)
  let Y (x : InversionClass n → Bool) (k : ZMod n) :=
    graftedActivationField (typesThroughSize D) M τ (scale D) (direction D) x k
  change average (fun x ↦ norm₂ (v x-signOperator x (smooth (weight n τ) (v x)))^2) ≤ _
  refine (average_mono (fun x ↦ norm_sq_smoothedTrialResidual_le hτ.le x (H D x) (P x) (Y x))).trans ?_
  simp only [average_mul_left,average_add,average_const]
  rw [average_average_comm (fun x k ↦ (H D x k - 2*leaf.representative.field x k-Y x k)^2),
    average_average_comm (fun x k ↦ (signOperator x (P x) k-Y x k)^2),
    average_average_comm (fun x k ↦ (P x k-activation τ (H D x k))^2)]
  exact mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (add_le_add (average_spatial_trialField_linearResidual_sq_le hτ hσ hσ' hMean hD hM p)
      (average_spatial_trialField_grafting_le hτ hσ hσ' hMean hD M))
      (average_spatial_trialField_activation_le hτ hσ hσ' hMean hD M hK hAct))
    (mul_le_mul_of_nonneg_left (add_le_add_left (average_sq_trialVector_zero_le hτ hσ hσ' hMean hD) _) (by norm_num)))
    (by norm_num)

end EvenTreeType

end LovaszTheta.Circulant
