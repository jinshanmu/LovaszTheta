module

public import LovaszTheta.TrialField
public import LovaszTheta.TrialExpectation

/-!
# Trial vector for the smoothed equation

Rescaling the truncated field turns its spatial mean square into
the Euclidean norm square. The smoothing parameter changes at
zero, producing a single correction in the direction of the origin.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

lemma norm₂_invSqrt_smul_sq_eq_average (z : ZMod n → ℝ) :
    norm₂ ((Real.sqrt (n : ℝ))⁻¹ • z)^2 = average (fun k ↦ (z k)^2) := by
  rw [norm₂_sq]
  simp only [dotProduct,Pi.smul_apply,smul_eq_mul,← pow_two,mul_pow,← mul_sum,inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),average,ZMod.card,div_eq_inv_mul]

omit [NeZero n] in
private lemma activation_sqrt_scale {τ : ℝ} (hτ : 0 ≤ τ) (z : ℝ) :
    activation (τ/(n : ℝ)) ((Real.sqrt (n : ℝ))⁻¹*z) =
      (Real.sqrt (n : ℝ))⁻¹*activation τ z := by
  unfold activation
  rw [mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  rw [show (n : ℝ)⁻¹*z^2+4*(τ/(n : ℝ)) = (z^2+4*τ)/(n : ℝ) by ring]
  rw [Real.sqrt_div (by positivity),div_eq_inv_mul]

/-- The scalar correction at the differently weighted origin. -/
noncomputable def originSmoothingError (τ : ℝ) (z : ZMod n → ℝ) : ℝ :=
  activation 1 ((Real.sqrt (n : ℝ))⁻¹*z 0) - (Real.sqrt (n : ℝ))⁻¹*activation τ (z 0) - 2

omit [NeZero n] in
lemma smooth_invSqrt_smul_eq {τ : ℝ} (hτ : 0 ≤ τ) (z : ZMod n → ℝ) :
    smooth (weight n τ) ((Real.sqrt (n : ℝ))⁻¹ • z) =
      (Real.sqrt (n : ℝ))⁻¹ • (fun k ↦ activation τ (z k)) +
        (2+originSmoothingError τ z) • Pi.single 0 1 := by
  funext k
  change activation (weight n τ k) ((Real.sqrt (n : ℝ))⁻¹*z k) =
    (Real.sqrt (n : ℝ))⁻¹*activation τ (z k)+(2+originSmoothingError τ z)*(Pi.single 0 1 : ZMod n → ℝ) k
  by_cases hk : k=0
  · subst k
    rw [weight_zero,Pi.single_eq_same,originSmoothingError]
    ring
  · rw [weight,ite_eq_right hk,Pi.single_eq_of_ne hk,mul_zero,add_zero,activation_sqrt_scale hτ]

omit [NeZero n] in
lemma abs_originSmoothingError_le {τ : ℝ} (hτ : 0 ≤ τ) (z : ZMod n → ℝ) :
    |originSmoothingError τ z| ≤
      2*|(Real.sqrt (n : ℝ))⁻¹*z 0|+2*Real.sqrt (τ/(n : ℝ)) := by
  let v := (Real.sqrt (n : ℝ))⁻¹*z 0
  have he : originSmoothingError τ z = (activation 1 v-2)-activation (τ/(n : ℝ)) v := by
    unfold originSmoothingError
    rw [← activation_sqrt_scale hτ]
    dsimp only [v]
    ring
  have hPos : 0 ≤ activation 1 v-2 := by
    have h : activation 1 0 ≤ activation 1 v := by
      apply Real.sqrt_le_sqrt
      nlinarith only [sq_nonneg v]
    rw [activation_zero,Real.sqrt_one,mul_one] at h
    exact sub_nonneg.mpr h
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hPos,abs_of_nonneg (activation_nonneg _ _)]
  have h₁ := activation_le_abs_add (by norm_num : (0 : ℝ) ≤ 1) v
  have h₂ := activation_le_abs_add (div_nonneg hτ (by positivity : (0 : ℝ) ≤ n)) v
  rw [Real.sqrt_one,mul_one] at h₁
  linarith only [h₁,h₂]

private lemma average_sq_atom_signOperator_le (x : InversionClass n → Bool) :
    average (fun k ↦ (signOperator x (Pi.single 0 1) k)^2) ≤ 1/(n : ℝ) := by
  refine (average_signOperator_sq_le x _).trans_eq ?_
  have he (k : ZMod n) : ((Pi.single 0 1 : ZMod n → ℝ) k)^2 = if k = 0 then 1 else 0 := by
    by_cases h : k = 0 <;> simp [h]
  simp_rw [he,average,Finset.sum_ite_eq',ite_eq_left (mem_univ _),ZMod.card]

/-- The norm of the residual is controlled by the four terms of
the decomposition of the smoothed equation. -/
theorem norm_sq_smoothedTrialResidual_le {τ : ℝ} (hτ : 0 ≤ τ) (x : InversionClass n → Bool)
    (z P Y : ZMod n → ℝ) :
    let v := (Real.sqrt (n : ℝ))⁻¹ • z
    norm₂ (v - signOperator x (smooth (weight n τ) v)) ^ 2 ≤
      4*(average (fun k ↦ (z k - 2*EvenTreeType.leaf.representative.field x k - Y k)^2) +
        average (fun k ↦ (signOperator x P k - Y k)^2) +
        average (fun k ↦ (P k-activation τ (z k))^2) +
        8*((v 0)^2+τ/(n : ℝ))) := by
  let s := Real.sqrt (n : ℝ)
  let v := s⁻¹ • z
  let a := z - (2 : ℝ) • EvenTreeType.leaf.representative.field x - Y
  let b := signOperator x P - Y
  let c := P - fun k ↦ activation τ (z k)
  let β := originSmoothingError τ z
  let e := (Pi.single 0 1 : ZMod n → ℝ)
  let d := (s*β) • signOperator x e
  have hPos : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  have hLeaf (k : ZMod n) : EvenTreeType.leaf.representative.field x k = s*signOperator x e k :=
    (EvenTreeType.leafIsomorphismSingle.field_eq x k).trans (RootedTree.single_field_eq_signOperator x k)
  have he : v-signOperator x (smooth (weight n τ) v) = s⁻¹ • (a-b+signOperator x c-d) := by
    rw [show smooth (weight n τ) v = s⁻¹ • (fun k ↦ activation τ (z k)) + (2+β) • e from
      smooth_invSqrt_smul_eq hτ z,map_add,map_smul,map_smul]
    unfold a b c d v
    rw [map_sub]
    funext k
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hLeaf]
    field_simp [hPos.ne']
    ring
  have hβ : β^2 ≤ 8*((v 0)^2+τ/(n : ℝ)) := by
    have h := abs_originSmoothingError_le hτ z
    change |β| ≤ 2*|v 0|+2*Real.sqrt (τ/(n : ℝ)) at h
    have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h'
    refine h'.trans ?_
    nlinarith only [sq_nonneg (|v 0|-Real.sqrt (τ/(n : ℝ))),sq_abs (v 0),
      Real.sq_sqrt (div_nonneg hτ (by positivity : (0 : ℝ) ≤ n))]
  have hd : average (fun k ↦ (d k)^2) ≤ β^2 := by
    simp only [d,Pi.smul_apply,smul_eq_mul,mul_pow,average_mul_left]
    refine (mul_le_mul_of_nonneg_left (average_sq_atom_signOperator_le x) (by positivity)).trans_eq ?_
    have hs : s^2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [hs]
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp [hn]
  have hPt (k : ZMod n) : (a k-b k+signOperator x c k-d k)^2 ≤
      4*((a k)^2+(b k)^2+(signOperator x c k)^2+(d k)^2) := by
    nlinarith only [sq_nonneg (a k+b k),sq_nonneg (a k-signOperator x c k),
      sq_nonneg (a k+d k),sq_nonneg (b k+signOperator x c k),sq_nonneg (b k-d k),
      sq_nonneg (signOperator x c k+d k)]
  change norm₂ (v-signOperator x (smooth (weight n τ) v))^2 ≤ _
  rw [he,norm₂_invSqrt_smul_sq_eq_average]
  refine (average_mono hPt).trans ?_
  simp_rw [average_mul_left,average_add]
  exact mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add_right (average_signOperator_sq_le x c) _) (hd.trans hβ)) (by norm_num)

namespace EvenTreeType

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))

/-- The normalized, real trial vector on the cyclic Fourier coordinates. -/
noncomputable def trialVector (D : ℕ) (x : InversionClass n → Bool) : ZMod n → ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ • trialField hτ hσ hσ' hMean D x

lemma trialVector_even (D : ℕ) (x : InversionClass n → Bool) :
    (trialVector hτ hσ hσ' hMean D x).Even := by
  intro k
  exact congrArg ((Real.sqrt (n : ℝ))⁻¹ * ·) (trialField_even hτ hσ hσ' hMean D x k)

lemma sum_trialVector (D : ℕ) (x : InversionClass n → Bool) :
    ∑ k, trialVector hτ hσ hσ' hMean D x k = 0 := by
  simp only [trialVector,Pi.smul_apply,smul_eq_mul,← mul_sum,sum_trialField,mul_zero]

theorem average_norm_sq_trialVector_le {D : ℕ} (hD : 0 < D) :
    average (fun x : InversionClass n → Bool ↦ norm₂ (trialVector hτ hσ hσ' hMean D x)^2) ≤
      (2*Real.pi)*(1+linearTransferError D n) := by
  simp only [trialVector,norm₂_invSqrt_smul_sq_eq_average,trialField]
  rw [average_average_comm]
  refine (average_spatial_evaluateCoefficients_sq_le D _
    (trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D)).trans ?_
  rw [norm_trialCoefficients hτ hσ hσ' hMean hD,gaussianSizeScale_eq_norm]
  exact mul_le_mul_of_nonneg_right (gaussianSizeProjection_variance_bounds hτ hσ hσ' hMean hD).2
    (by linarith only [linearTransferError_nonneg D n])

theorem average_sq_trialVector_zero_le {D : ℕ} (hD : 0 < D) :
    average (fun x : InversionClass n → Bool ↦ (trialVector hτ hσ hσ' hMean D x 0)^2) ≤
      (2*Real.pi)*((4 : ℝ)^D*treeMomentEnvelope D)/(n : ℝ) := by
  simp only [trialVector,Pi.smul_apply,smul_eq_mul,mul_pow,average_mul_left,inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),trialField,div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (average_evaluateCoefficients_sq_le D _
    (trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D) 0).trans ?_
  rw [norm_trialCoefficients hτ hσ hσ' hMean hD,gaussianSizeScale_eq_norm]
  exact mul_le_mul_of_nonneg_right (gaussianSizeProjection_variance_bounds hτ hσ hσ' hMean hD).2
    (by unfold treeMomentEnvelope; positivity)

end EvenTreeType

end LovaszTheta.Circulant
