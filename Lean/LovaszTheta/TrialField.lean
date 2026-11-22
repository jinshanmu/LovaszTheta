module

public import LovaszTheta.ActivationSpatial
public import LovaszTheta.FiniteTreeSeries
public import LovaszTheta.GaussianProjectionResidual
public import LovaszTheta.GraftActivationProjection

/-!
# Finite trial fields

The trial field is the Gaussian size projection with each
Gaussian coordinate replaced by its tree field. The linear
Gaussian residual is supported on sizes through `1 + D*M`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.EvenTreeType

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))

local notation "scale" => gaussianSizeScale hτ hσ hσ' hMean
local notation "direction" => gaussianSizeDirection hτ hσ hσ' hMean

/-- The finite Gaussian coefficients with their original normalization. -/
noncomputable def trialCoefficients (D : ℕ) : lp (fun _ : EvenTreeType ↦ ℝ) 2 :=
  scale D • direction D

lemma trialCoefficients_apply_of_notMem (D : ℕ) (T : EvenTreeType) (hT : T ∉ typesThroughSize D) :
    trialCoefficients hτ hσ hσ' hMean D T = 0 := by
  simp only [trialCoefficients,lp.coeFn_smul,Pi.smul_apply,
    gaussianSizeDirection_apply_of_notMem hτ hσ hσ' hMean D T hT,smul_zero]

lemma norm_trialCoefficients {D : ℕ} (hD : 0 < D) :
    ‖trialCoefficients hτ hσ hσ' hMean D‖ = scale D := by
  have h := zero_lt_two.trans_le (gaussianSizeScale_bounds hτ hσ hσ' hMean hD).1
  rw [trialCoefficients,norm_smul,Real.norm_eq_abs,abs_of_pos h,norm_gaussianSizeDirection hτ hσ hσ' hMean hD,mul_one]

/-- The Gaussian residual coefficients, using the exact finite expansion of the projection. -/
noncomputable def gaussianResidualCoefficients (D M : ℕ) : lp (fun _ : EvenTreeType ↦ ℝ) 2 :=
  trialCoefficients hτ hσ hσ' hMean D - lp.single 2 leaf 2 -
    ∑ m ∈ finiteHermiteProducts (typesThroughSize D) M, lp.single 2 (graftOfIndex m)
      (activationHermiteProductCoeff τ (scale D) (direction D) m.val)

private lemma graftOfIndex_mem_size {D M : ℕ} {m : PositiveEvenHermiteIndex EvenTreeType}
    (hm : m ∈ finiteHermiteProducts (typesThroughSize D) M) :
    graftOfIndex m ∈ typesThroughSize (1+D*M) := by
  have h := mem_finiteHermiteProducts.mp hm
  apply (mem_typesThroughSize _ _).mpr
  rw [← representative_nodeCount]
  exact graft_nodeCount_le m D M (fun T hT ↦ (mem_typesThroughSize _ _).mp (h.1 hT)) h.2

private lemma typesThroughSize_subset_graftSize (D : ℕ) {M : ℕ} (hM : 0 < M) :
    typesThroughSize D ⊆ typesThroughSize (1+D*M) := by
  intro T hT
  apply (mem_typesThroughSize _ _).mpr
  have hProduct : D*1 ≤ D*M := Nat.mul_le_mul_left D (Nat.succ_le_of_lt hM)
  rw [mul_one] at hProduct
  exact ((mem_typesThroughSize _ _).mp hT).trans (by omega)

lemma gaussianResidualCoefficients_apply_of_notMem (D M : ℕ) (hM : 0 < M)
    (T : EvenTreeType) (hT : T ∉ typesThroughSize (1+D*M)) :
    gaussianResidualCoefficients hτ hσ hσ' hMean D M T = 0 := by
  have hLeaf : T ≠ leaf := by
    rintro rfl
    exact hT ((mem_typesThroughSize _ _).mpr (by rw [nodeCount_leaf]; omega))
  have hSmall : T ∉ typesThroughSize D := fun h ↦ hT (typesThroughSize_subset_graftSize D hM h)
  let f (m : PositiveEvenHermiteIndex EvenTreeType) : lp (fun _ : EvenTreeType ↦ ℝ) 2 := lp.single 2 (graftOfIndex m)
    (activationHermiteProductCoeff τ (scale D) (direction D) m.val)
  have hn : (∑ m ∈ finiteHermiteProducts (typesThroughSize D) M, f m) T = 0 := by
    rw [lp.coeFn_sum]
    change (∑ m ∈ finiteHermiteProducts (typesThroughSize D) M, (fun k ↦ f m k)) T = 0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro m hm
    have hne : T ≠ graftOfIndex m := fun he ↦ hT (by rw [he]; exact graftOfIndex_mem_size hm)
    dsimp only [f]
    rw [lp.single_apply,Pi.single_eq_of_ne hne]
  change (trialCoefficients hτ hσ hσ' hMean D-lp.single 2 leaf 2-
    ∑ m ∈ finiteHermiteProducts (typesThroughSize D) M, f m : lp (fun _ : EvenTreeType ↦ ℝ) 2) T = 0
  simp only [lp.coeFn_sub,Pi.sub_apply,trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D T hSmall,
    lp.single_apply,Pi.single_eq_of_ne hLeaf,hn,sub_zero]

/-- The norm bound on the finite array is the norm bound from the Gaussian equation. -/
theorem norm_sq_gaussianResidualCoefficients_le {D : ℕ} (hD : 0 < D) (M : ℕ) (p : ℕ) :
    ‖gaussianResidualCoefficients hτ hσ hσ' hMean D M‖^2 ≤
      6*(σ^2 * (∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) / (D : ℝ)^p)
      + 3*(∑' j : ℕ, activationCoefficient τ (scale D) (j+(M+1))^2) := by
  let S := gaussianSeries EvenTreeType
  rw [← S.norm_map (gaussianResidualCoefficients hτ hσ hσ' hMean D M)]
  have he (T : EvenTreeType) (a : ℝ) : S (lp.single 2 T a) = a • gaussianCoordinateL2 T :=
    orthonormalSeries_single orthonormal_gaussianCoordinateL2 T a
  simp only [gaussianResidualCoefficients,map_sub,map_sum,he,trialCoefficients,map_smul]
  rw [gaussianSizeScale_smul_series hτ hσ hσ' hMean hD]
  exact (norm_sq_gaussianProjection_residual_le hτ hσ hσ' hMean hD M).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (gaussianSizeProjection_error_le hτ hσ hσ' hMean hD p)
      (by norm_num : (0 : ℝ) ≤ 6)) _)

variable {n : ℕ} [NeZero n]

/-- The scalar vector of the finitely many tree fields in the size-truncated Gaussian. -/
noncomputable def trialField (D : ℕ) (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  evaluateCoefficients (typesThroughSize D) x k (trialCoefficients hτ hσ hσ' hMean D)

lemma trialField_eq_sum (D : ℕ) (x : InversionClass n → Bool) (k : ZMod n) :
    trialField hτ hσ hσ' hMean D x k =
      scale D * ∑ T ∈ typesThroughSize D, direction D T*T.representative.field x k := by
  simp only [trialField,trialCoefficients,map_smul,smul_eq_mul,evaluateCoefficients_apply]

lemma trialField_even (D : ℕ) (x : InversionClass n → Bool) :
    (trialField hτ hσ hσ' hMean D x).Even := evaluateCoefficients_even _ _ _

lemma sum_trialField (D : ℕ) (x : InversionClass n → Bool) :
    ∑ k, trialField hτ hσ hσ' hMean D x k = 0 := sum_evaluateCoefficients _ _ _

lemma evaluate_gaussianResidualCoefficients (D M : ℕ) (hM : 0 < M)
    (x : InversionClass n → Bool) (k : ZMod n) :
    evaluateCoefficients (typesThroughSize (1+D*M)) x k (gaussianResidualCoefficients hτ hσ hσ' hMean D M) =
      trialField hτ hσ hσ' hMean D x k - 2*leaf.representative.field x k -
        graftedActivationField (typesThroughSize D) M τ (scale D) (direction D) x k := by
  let E := evaluateCoefficients (typesThroughSize (1+D*M)) x k
  have hLeaf : leaf ∈ typesThroughSize (1+D*M) := (mem_typesThroughSize _ _).mpr (by rw [nodeCount_leaf]; omega)
  change E _ = _
  rw [gaussianResidualCoefficients,map_sub,map_sub,map_sum]
  have he : E (trialCoefficients hτ hσ hσ' hMean D) = trialField hτ hσ hσ' hMean D x k :=
    (evaluateCoefficients_mono_set (typesThroughSize_subset_graftSize D hM) x k _
      (trialCoefficients_apply_of_notMem hτ hσ hσ' hMean D)).symm
  rw [he,show E (lp.single 2 leaf 2) = _ from evaluateCoefficients_single hLeaf x k 2]
  congr 1
  exact sum_congr rfl fun m hm ↦ evaluateCoefficients_single (graftOfIndex_mem_size hm) x k _

/-- Spatial mean square for the linear residual from the Gaussian equation. -/
theorem average_spatial_trialField_linearResidual_sq_le {D M : ℕ} (hD : 0 < D)
    (hM : 0 < M) (p : ℕ) :
    average (fun k : ZMod n ↦ average (fun x ↦
      (trialField hτ hσ hσ' hMean D x k - 2*leaf.representative.field x k -
        graftedActivationField (typesThroughSize D) M τ (scale D) (direction D) x k)^2)) ≤
      (6*(σ^2 * (∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) / (D : ℝ)^p)
      + 3*(∑' j : ℕ, activationCoefficient τ (scale D) (j+(M+1))^2)) *
        (1+linearTransferError (1+D*M) n) := by
  simp_rw [← evaluate_gaussianResidualCoefficients hτ hσ hσ' hMean D M hM]
  exact (average_spatial_evaluateCoefficients_sq_le (1+D*M) _
    (gaussianResidualCoefficients_apply_of_notMem hτ hσ hσ' hMean D M hM)).trans
      (mul_le_mul_of_nonneg_right (norm_sq_gaussianResidualCoefficients_le hτ hσ hσ' hMean hD M p)
        (by linarith only [linearTransferError_nonneg (1+D*M) n]))

end LovaszTheta.Circulant.EvenTreeType
