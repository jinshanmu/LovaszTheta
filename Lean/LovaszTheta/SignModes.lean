module

public import LovaszTheta.Projections

/-!
# The sign multiplier on Fourier modes

The difference of the two projections multiplies a Fourier mode
by the sign of its residue. At zero the multiplier vanishes.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The spatial wave with residue `s` in the negative exponent convention. -/
noncomputable def characterMode (s : ZMod n) (k : ZMod n) : ℂ := ZMod.stdAddChar (-(s*k))

lemma multiplier_apply_eq_sum (a : ZMod n → ℂ) (i j : ZMod n) :
    multiplier a i j = (n : ℂ)⁻¹ * ∑ s, a s * characterMode s (i-j) := by
  rw [multiplier, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,fourierMatrix_conjTranspose_apply, fourierMatrix, characterMode]
  congr 1
  apply sum_congr rfl
  intro s _
  rw [mul_comm (ZMod.stdAddChar (-(i*s))) (a s), mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

lemma multiplier_mulVec_characterMode (a : ZMod n → ℂ) (s : ZMod n) :
    multiplier a *ᵥ characterMode s = a s • characterMode s := by
  let v : ZMod n → ℂ := Pi.single s 1
  let F := fourierMatrix n
  have hF : F *ᵥ v = characterMode s := by
    rw [Matrix.mulVec_single_one]
    funext k
    simp [F, fourierMatrix, characterMode, mul_comm]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  calc
    _ = (n : ℂ)⁻¹ • (F *ᵥ (diagonal a *ᵥ ((Fᴴ * F) *ᵥ v))) := by
      rw [← hF, multiplier, Matrix.smul_mulVec]
      simp only [F, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by
      rw [show Fᴴ * F = (n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) from fourierMatrix_conjTranspose_mul,
        Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_assoc, smul_eq_mul,
        inv_mul_cancel₀ hn, one_smul]
      rw [show diagonal a *ᵥ v = a s • v by
          rw [Matrix.diagonal_mulVec_single]
          funext k
          by_cases hk : k = s <;> simp [v,hk],
        Matrix.mulVec_smul,hF]

/-- The complexification of the real sign operator is the Fourier multiplier. -/
lemma signOperator_complexification (x : InversionClass n → Bool) (v : ZMod n → ℝ) :
    (fun k ↦ (signOperator x v k : ℂ)) = multiplier (fun s ↦ (epsilon x s : ℂ)) *ᵥ (fun k ↦ (v k : ℂ)) := by
  have hC (S : Set (ZMod n)) (hS : ∀ s, -s ∈ S ↔ s ∈ S) :
      (fun k ↦ ((realProjection S *ᵥ v) k : ℂ)) = fourierProjection S *ᵥ (fun k ↦ (v k : ℂ)) := by
    have h := funext (RingHom.map_mulVec Complex.ofRealHom (realProjection S) v)
    change _ = (realProjection S).map Complex.ofReal *ᵥ _ at h
    rwa [complexify_realProjection S hS] at h
  have hPD : fourierProjection (nonconnectionSet x) - fourierProjection (connectionSet x) =
      multiplier (fun s ↦ (epsilon x s : ℂ)) := by
    unfold fourierProjection multiplier
    rw [← smul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    congr 4
    funext s
    change (if epsilon x s = 1 then (1 : ℂ) else 0) - (if epsilon x s = -1 then 1 else 0) = _
    by_cases hs : s = 0
    · simp [hs]
    · cases h : x (inversionClass s hs) <;> norm_num [epsilon, hs, h, sign]
  rw [← hPD, Matrix.sub_mulVec, ← hC _ (connectionSet_even x), ← hC _ (nonconnectionSet_even x)]
  funext k
  simp only [signOperator_apply, Pi.sub_apply, Complex.ofReal_sub]

/-- In particular, the image of the origin atom is the normalized
exponential sum of the sign symbol. -/
lemma signOperator_origin (x : InversionClass n → Bool) (k : ZMod n) :
    (signOperator x (Pi.single 0 1) k : ℂ) =
      (n : ℂ)⁻¹ * ∑ s, (epsilon x s : ℂ) * characterMode s k := by
  have h := congrFun (signOperator_complexification x (Pi.single 0 1)) k
  have hv : (fun k : ZMod n ↦ ((Pi.single 0 1 : ZMod n → ℝ) k : ℂ)) = Pi.single 0 1 := by
    funext j
    by_cases hj : j = 0 <;> simp [hj]
  rw [hv, Matrix.mulVec_single_one] at h
  rw [h]
  exact (multiplier_apply_eq_sum _ _ _).trans (by rw [sub_zero])

end LovaszTheta.Circulant
