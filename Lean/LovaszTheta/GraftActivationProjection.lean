module

public import LovaszTheta.FiniteHermiteProducts
public import LovaszTheta.GraftResidualBound
public import LovaszTheta.SignModes

/-!
# Grafting the activation projection

Linearity removes the constant term and reduces the discrepancy
to a finite combination of the individual Hermite-product
residuals. Cauchy–Schwarz bounds the spatial mean square.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The sign operator annihilates constants, the zero Fourier mode. -/
lemma signOperator_const (x : InversionClass n → Bool) (c : ℝ) :
    signOperator x (fun _ ↦ c) = 0 := by
  have hMode : characterMode (0 : ZMod n) = fun _ ↦ (1 : ℂ) := by
    funext k
    simp [characterMode]
  have h := signOperator_complexification x (fun _ ↦ (1 : ℝ))
  simp only [Complex.ofReal_one,← hMode,multiplier_mulVec_characterMode,epsilon_zero,Complex.ofReal_zero,
    zero_smul] at h
  have hOne : signOperator x (fun _ ↦ (1 : ℝ)) = 0 := by
    funext k
    exact Complex.ofReal_injective (congrFun h k)
  rw [show (fun _ : ZMod n ↦ c) = c • (fun _ ↦ (1 : ℝ)) by ext; simp, map_smul,hOne,smul_zero]

namespace EvenTreeType

/-- The finite array of grafted tree fields obtained from the Hermite projection. -/
noncomputable def graftedActivationField (s : Finset EvenTreeType) (M : ℕ) (τ v : ℝ) (u : EvenTreeType → ℝ)
    (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  ∑ m ∈ finiteHermiteProducts s M, activationHermiteProductCoeff τ v u m.val *
    (graftOfIndex m).representative.field x k

/-- The mean-square transfer for the entire activation projection. -/
theorem average_spatial_sq_graftedActivationField_le [Nonempty (InversionClass n)]
    (S : Finset EvenTreeType) (D M : ℕ) (hD : ∀ i ∈ S, i.nodeCount ≤ D)
    {τ v : ℝ} (hτ : 0 ≤ τ) (hv : v ≠ 0) (u : EvenTreeType → ℝ) (hu : ∑ i ∈ S, u i^2 = 1) :
    let H (x : InversionClass n → Bool) (k : ZMod n) :=
      v*(∑ i ∈ S, u i*i.representative.field x k)
    average (fun k : ZMod n ↦ average (fun x ↦
      (signOperator x (fun j ↦ activationProjection τ v M (H x j)) k -
        graftedActivationField S M τ v u x k)^2)) ≤
      (v^2+4*τ)*((S.card : ℝ)+1)^M*graftResidualError D M n := by
  let H (x : InversionClass n → Bool) (k : ZMod n) := v*(∑ i ∈ S, u i*i.representative.field x k)
  let c (m : PositiveEvenHermiteIndex EvenTreeType) := activationHermiteProductCoeff τ v u m.val
  let F := finiteHermiteProducts S M
  let R (m : PositiveEvenHermiteIndex EvenTreeType) (x : InversionClass n → Bool) (k : ZMod n) :=
    signOperator x (hermiteField m.val x) k - (graftOfIndex m).representative.field x k
  have he (x : InversionClass n → Bool) :
      (fun j ↦ activationProjection τ v M (H x j)) =
        (fun _ ↦ activationMean τ v) +
          ∑ m ∈ F, c m • hermiteField m.val x := by
    funext j
    rw [Pi.add_apply,Finset.sum_apply]
    exact activationProjection_eq_hermiteProducts hv S M u (fun i ↦ i.representative.field x j) hu
  have hR (x : InversionClass n → Bool) (k : ZMod n) :
        signOperator x (fun j ↦ activationProjection τ v M (H x j)) k -
          graftedActivationField S M τ v u x k = ∑ m ∈ F, c m*R m x k := by
    rw [he,map_add,signOperator_const,zero_add,map_sum,Finset.sum_apply,graftedActivationField,← sum_sub_distrib]
    simp only [R,c,map_smul,Pi.smul_apply,smul_eq_mul,mul_sub,F]
  have hEach (m : PositiveEvenHermiteIndex EvenTreeType) (hm : m ∈ F) :
      average (fun k : ZMod n ↦ average (fun x ↦ R m x k ^ 2)) ≤ graftResidualError D M n := by
    have h := mem_finiteHermiteProducts.mp hm
    exact average_spatial_sq_graftResidual_le m D M (fun t ht ↦ hD t (h.1 ht)) h.2
  have hCn : 0 ≤ ∑ m ∈ F, c m ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : 0 ≤ graftResidualError D M n := by
    unfold graftResidualError graftProductErrorScale comparisonEnvelope treeMomentEnvelope
    positivity
  change average (fun k ↦ average (fun x ↦
    (signOperator x (fun j ↦ activationProjection τ v M (H x j)) k -
      graftedActivationField S M τ v u x k)^2)) ≤ _
  simp_rw [hR]
  calc
    _ ≤ average (fun k ↦ average (fun x ↦ (∑ m ∈ F, c m^2)*(∑ m ∈ F, R m x k^2))) :=
      average_mono fun k ↦ average_mono fun x ↦ sum_mul_sq_le_sq_mul_sq F c (fun m ↦ R m x k)
    _ = (∑ m ∈ F, c m^2)*(∑ m ∈ F, average (fun k ↦ average (fun x ↦ R m x k^2))) := by
      simp_rw [average_mul_left,average_finsetSum]
    _ ≤ (v^2+4*τ)*(F.card*graftResidualError D M n) := by
      apply mul_le_mul (sum_sq_activationHermiteProductCoeff_le hτ S M u hu)
      · exact (sum_le_sum hEach).trans_eq (by rw [sum_const,nsmul_eq_mul])
      · exact sum_nonneg fun _ _ ↦ average_nonneg (fun _ ↦ average_sq_nonneg _)
      · positivity
    _ ≤ _ := by
      rw [mul_assoc]
      have h : (F.card : ℝ) ≤ ((S.card : ℝ)+1)^M := by exact_mod_cast card_finiteHermiteProducts_le S M
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hB) (by positivity)

end EvenTreeType

end LovaszTheta.Circulant
