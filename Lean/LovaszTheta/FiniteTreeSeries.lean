module

public import LovaszTheta.GaussianSizeProjection
public import LovaszTheta.LinearTransfer

/-!
# Finite restrictions of Gaussian linear series to the sign fields

The norm of the coefficient vector is the Gaussian L² norm.
Replacing the Gaussian coordinates by the associated tree fields
then uses the finite spatial linear transfer.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.EvenTreeType

variable {n : ℕ} [NeZero n]

/-- Evaluation of a finite Gaussian coefficient array on the tree fields. -/
noncomputable def evaluateCoefficients (s : Finset EvenTreeType) (x : InversionClass n → Bool) (k : ZMod n) :
    lp (fun _ : EvenTreeType ↦ ℝ) 2 →ₗ[ℝ] ℝ where
  toFun a := ∑ T ∈ s, a T*T.representative.field x k
  map_add' a b := by simp only [lp.coeFn_add,Pi.add_apply,add_mul,sum_add_distrib]
  map_smul' c a := by simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_sum,RingHom.id_apply]

lemma evaluateCoefficients_apply (s : Finset EvenTreeType) (x : InversionClass n → Bool) (k : ZMod n)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) :
    evaluateCoefficients s x k a = ∑ T ∈ s, a T*T.representative.field x k := rfl

lemma evaluateCoefficients_eq_treeLinearEvaluation (s : Finset EvenTreeType)
    (x : InversionClass n → Bool) (k : ZMod n) (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) :
    evaluateCoefficients s x k a = treeLinearEvaluation (fun T : s ↦ a T.val)
      (fun T ↦ T.val.representative) x k :=
  (sum_coe_sort s fun T ↦ a T*T.representative.field x k).symm

lemma evaluateCoefficients_mono_set {s t : Finset EvenTreeType} (hst : s ⊆ t)
    (x : InversionClass n → Bool) (k : ZMod n)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) (ha : ∀ T ∉ s, a T = 0) :
    evaluateCoefficients s x k a = evaluateCoefficients t x k a := by
  simp only [evaluateCoefficients_apply]
  exact sum_subset hst fun i _ hi ↦ by rw [ha i hi,zero_mul]

lemma evaluateCoefficients_single {s : Finset EvenTreeType} {T : EvenTreeType} (hT : T ∈ s)
    (x : InversionClass n → Bool) (k : ZMod n) (a : ℝ) :
    evaluateCoefficients s x k (lp.single 2 T a) = a*T.representative.field x k := by
  rw [evaluateCoefficients_apply, sum_eq_single_of_mem T hT]
  · rw [lp.single_apply,Pi.single_eq_same]
  · intro i _ hi
    rw [lp.single_apply,Pi.single_eq_of_ne hi,zero_mul]

lemma evaluateCoefficients_even (s : Finset EvenTreeType) (x : InversionClass n → Bool)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) :
    (fun k ↦ evaluateCoefficients s x k a).Even := by
  intro k
  exact sum_congr rfl fun T _ ↦ congrArg (a T * ·) (T.representative.field_even x k)

lemma sum_evaluateCoefficients (s : Finset EvenTreeType) (x : InversionClass n → Bool)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) :
    ∑ k, evaluateCoefficients s x k a = 0 := by
  simp only [evaluateCoefficients_apply]
  rw [sum_comm]
  simp only [← mul_sum,RootedTree.sum_field,mul_zero,sum_const_zero]

/-- The relative error in transferring a squared Gaussian norm. -/
noncomputable def linearTransferError (D n : ℕ) : ℝ :=
  (4 : ℝ)^D*(treeMomentEnvelope D / Real.sqrt n + (treeMomentEnvelope D+1)*(2/(n : ℝ)))

lemma linearTransferError_nonneg (D n : ℕ) : 0 ≤ linearTransferError D n := by
  unfold linearTransferError treeMomentEnvelope
  positivity

/-- The linear transfer in terms of square-summable coefficients with finite size support. -/
theorem average_spatial_evaluateCoefficients_sq_le (D : ℕ)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) (ha : ∀ T ∉ typesThroughSize D, a T = 0) :
    average (fun k : ZMod n ↦ average (fun x ↦ (evaluateCoefficients (typesThroughSize D) x k a)^2)) ≤
      ‖a‖^2*(1+linearTransferError D n) := by
  let s := typesThroughSize D
  have h := abs_average_spatial_treeLinearEvaluation_sq_sub_le
    (fun T : s ↦ a T.val) (fun T ↦ T.val.representative)
    (fun T ↦ (representative_nodeCount _).trans_le ((mem_typesThroughSize _ _).mp T.property))
    (fun T U e ↦ Subtype.ext ((representative_isomorphism_iff U.val T.val).mp e).symm) (n := n)
  have he : (∑ T : s, a T.val ^ 2) = ‖a‖^2 :=
    (sum_coe_sort s fun T ↦ a T ^ 2).trans (sum_sq_eq_gaussianCoefficient_norm_sq ha)
  rw [he,Fintype.card_coe] at h
  have hC : (s.card : ℝ) ≤ (4 : ℝ)^D := by exact_mod_cast card_typesThroughSize_le D
  have hE : 0 ≤ treeMomentEnvelope D / Real.sqrt n + (treeMomentEnvelope D+1)*(2/(n : ℝ)) := by
    unfold treeMomentEnvelope
    positivity
  simp_rw [evaluateCoefficients_eq_treeLinearEvaluation]
  calc
    _ ≤ ‖a‖^2 + (s.card*‖a‖^2)*(treeMomentEnvelope D / Real.sqrt n +
        (treeMomentEnvelope D+1)*(2/(n : ℝ))) := by linarith only [(le_abs_self _).trans h]
    _ ≤ ‖a‖^2 + ((4 : ℝ)^D*‖a‖^2)*(treeMomentEnvelope D / Real.sqrt n +
        (treeMomentEnvelope D+1)*(2/(n : ℝ))) :=
      add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg _)) hE) _
    _ = _ := by unfold linearTransferError; ring

/-- The linear transfer bound at one arbitrary frequency, including zero. -/
theorem average_evaluateCoefficients_sq_le (D : ℕ)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) (ha : ∀ T ∉ typesThroughSize D, a T = 0) (k : ZMod n) :
    average (fun x ↦ (evaluateCoefficients (typesThroughSize D) x k a)^2) ≤
      ‖a‖^2*((4 : ℝ)^D*treeMomentEnvelope D) := by
  let s := typesThroughSize D
  have h := average_treeLinearEvaluation_sq_le
    (fun T : s ↦ a T.val) (fun T ↦ T.val.representative) k
    (fun T ↦ (representative_nodeCount _).trans_le ((mem_typesThroughSize _ _).mp T.property))
  have he : (∑ T : s, a T.val ^ 2) = ‖a‖^2 :=
    (sum_coe_sort s fun T ↦ a T ^ 2).trans (sum_sq_eq_gaussianCoefficient_norm_sq ha)
  rw [he,Fintype.card_coe] at h
  have hC : (s.card : ℝ) ≤ (4 : ℝ)^D := by exact_mod_cast card_typesThroughSize_le D
  simp_rw [evaluateCoefficients_eq_treeLinearEvaluation]
  exact h.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
    (by unfold treeMomentEnvelope; positivity)).trans_eq (by ring))

end LovaszTheta.Circulant.EvenTreeType
