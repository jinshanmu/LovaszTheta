module

public import LovaszTheta.HermiteFieldGrafting
public import LovaszTheta.PolarizedMoments

/-!
# Spatial energies of the graft residual

The sign operator is self-adjoint and its square subtracts the
constant projection. Combined with Walsh orthogonality this
expresses the residual through one- and two-frequency averages.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

lemma average_signOperator_sq (x : InversionClass n → Bool) (v : ZMod n → ℝ) :
    average (fun k ↦ (signOperator x v k)^2) = average (fun k ↦ (v k)^2) - (average v)^2 := by
  have he := signOperator_selfAdjoint x v (signOperator x v)
  rw [signOperator_square,dotProduct_sub] at he
  have hμ : (v ⬝ᵥ meanVector v) / Fintype.card (ZMod n) = (average v)^2 := by
    unfold dotProduct meanVector mass average
    rw [← sum_mul]
    ring
  simp only [pow_two]
  change (signOperator x v ⬝ᵥ signOperator x v) / Fintype.card (ZMod n) =
    (v ⬝ᵥ v) / Fintype.card (ZMod n) - (average v)*(average v)
  rw [he,sub_div,hμ,pow_two]

lemma average_sq_average_eq_double (v : ZMod n → ℝ) :
    (average v)^2 = average (fun k ↦ average (fun j ↦ v k*v j)) := by
  simp only [average_mul_left, pow_two]
  simp_rw [mul_comm _ (average v),average_mul_left]

/-- The square of the sign-operator output is no larger than the input square. -/
lemma average_signOperator_sq_le (x : InversionClass n → Bool) (v : ZMod n → ℝ) :
    average (fun k ↦ (signOperator x v k)^2) ≤ average (fun k ↦ (v k)^2) := by
  rw [average_signOperator_sq]
  exact sub_le_self _ (sq_nonneg _)

/-- Exact spatial residual energy, before applying the Gaussian comparison. -/
theorem EvenTreeType.average_spatial_sq_graftResidual (m : PositiveEvenHermiteIndex EvenTreeType) :
    average (fun k : ZMod n ↦ average (fun x ↦
      (signOperator x (hermiteField m.val x) k - (graftOfIndex m).representative.field x k)^2)) =
      average (fun k : ZMod n ↦ average (fun x ↦ (hermiteField m.val x k)^2)) -
        average (fun k : ZMod n ↦ average (fun j : ZMod n ↦
          average (fun x ↦ hermiteField m.val x k*hermiteField m.val x j))) -
      average (fun k : ZMod n ↦ average (fun x ↦ ((graftOfIndex m).representative.field x k)^2)) := by
  simp_rw [average_sq_graftResidual,average_sub]
  rw [average_average_comm (fun k x ↦ (signOperator x (hermiteField m.val x) k)^2)]
  simp_rw [average_signOperator_sq,average_sub,average_sq_average_eq_double]
  rw [average_average_comm (fun x (k : ZMod n) ↦ (hermiteField m.val x k)^2)]
  rw [average_average_comm (fun x (k : ZMod n) ↦ average (fun j ↦ hermiteField m.val x k*hermiteField m.val x j))]
  have h (k : ZMod n) := average_average_comm (fun x (j : ZMod n) ↦ hermiteField m.val x k*hermiteField m.val x j)
  simp_rw [h]

end LovaszTheta.Circulant
