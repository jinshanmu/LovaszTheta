module

public import LovaszTheta.TreeDerivativeVariance

/-!
# A common envelope for the tree moment bounds

A single function of the maximum node count bounds the second moments,
single-sign derivative energies, and the variances of the derivative
pairings.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- An explicit choice of the manuscript's size-dependent moment envelope. -/
noncomputable def treeMomentEnvelope (D : ℕ) : ℝ :=
  (2 * (D : ℝ)) ^ (14*D)

lemma treeMomentEnvelope_eq_exp {D : ℕ} (hD : 0 < D) :
    treeMomentEnvelope D = Real.exp (14 * (D : ℝ) * Real.log (2 * D)) := by
  have h0 : 0 < (2 : ℝ) * D := by positivity
  unfold treeMomentEnvelope
  rw [show 14 * (D : ℝ) = ((14 * D : ℕ) : ℝ) by push_cast; rfl,
    Real.exp_nat_mul, Real.exp_log h0]

private lemma unmatchedDerivativeConstant_le (T S : RootedTree) {D : ℕ}
    (hT : T.nodeCount ≤ D) (hS : S.nodeCount ≤ D) :
    unmatchedDerivativeConstant T S ≤ (2 * (D : ℝ)) ^ (10*D+2) := by
  let z := 2 * (D : ℝ)
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (T.nodeCount_pos.trans_le hT)
  have hT' : (T.nodeCount : ℝ) ≤ D := by exact_mod_cast hT
  have hS' : (S.nodeCount : ℝ) ≤ D := by exact_mod_cast hS
  have hz : 2 ≤ z := by dsimp [z]; linarith
  have hz₁ : 1 ≤ z := by linarith
  have hZ₂ : (4 : ℝ) ≤ z^2 := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hz 2
  have hZ₃ : 4 * z ≤ z^3 := by
    simpa only [pow_succ z 2] using mul_le_mul_of_nonneg_right hZ₂ (by positivity : 0 ≤ z)
  have hPairBase : 1 + 2*((T.nodeCount : ℝ)+(S.nodeCount : ℝ)) ≤ z^3 := by
    apply le_trans _ hZ₃
    dsimp [z]
    linarith
  have hCodeBase : 1 + 2*(S.nodeCount : ℝ) ≤ z^2 := by
    have hMul := mul_le_mul_of_nonneg_right hz (by positivity : 0 ≤ z)
    dsimp [z] at *
    nlinarith only [hMul, hD, hS']
  have hPairs :
      (1 + 2*((T.nodeCount : ℝ)+(S.nodeCount : ℝ)))^(T.nodeCount + S.nodeCount) ≤ z^(6*D) := by
    calc
      _ ≤ (z^3)^(T.nodeCount+S.nodeCount) := pow_le_pow_left₀ (by positivity) hPairBase _
      _ ≤ (z^3)^(2*D) := pow_le_pow_right₀ (one_le_pow₀ hz₁) (by omega)
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hCodes : ((1+2*(S.nodeCount : ℝ)) ^ T.nodeCount)^2 ≤ z^(4*D) := by
    have he : (1+2*(S.nodeCount : ℝ))^T.nodeCount ≤ (z^2)^D :=
      (pow_le_pow_left₀ (by positivity) hCodeBase _).trans
        (pow_le_pow_right₀ (one_le_pow₀ hz₁) hT)
    have hs := pow_le_pow_left₀ (by positivity) he 2
    calc
      _ ≤ ((z^2)^D)^2 := hs
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; omega
  have hNodes : (T.nodeCount : ℝ)^2 ≤ z^2 :=
    pow_le_pow_left₀ (by positivity) (by dsimp [z]; linarith) _
  unfold unmatchedDerivativeConstant
  push_cast
  calc
    _ ≤ z^2 * z^(6*D) * z^(4*D) := by gcongr
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

private lemma leafCount_le_nodeCount (T : RootedTree) : Fintype.card T.Leaf ≤ T.nodeCount := by
  have h := Fintype.card_le_of_injective (fun u : T.Leaf ↦ u.val) Subtype.val_injective
  simpa only [Fintype.card_fin] using h

lemma tree_base_moment_le (T : RootedTree) {D : ℕ} (hT : T.nodeCount ≤ D) :
    ((2 * T.nodeCount : ℕ) : ℝ) ^ Fintype.card T.Leaf ≤ (2 * (D : ℝ))^D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (T.nodeCount_pos.trans_le hT)
  have hC : ((2 * T.nodeCount : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hT
  exact (pow_le_pow_left₀ (by positivity) hC _).trans
    (pow_le_pow_right₀ (by linarith) ((leafCount_le_nodeCount T).trans hT))

variable {n : ℕ} [NeZero n]

/-- Tree coordinate second moments share the same size envelope. -/
theorem average_field_sq_le_envelope (T : RootedTree) (k : ZMod n) {D : ℕ} (hT : T.nodeCount ≤ D) :
    average (fun x ↦ T.field x k ^ 2) ≤ treeMomentEnvelope D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (T.nodeCount_pos.trans_le hT)
  unfold treeMomentEnvelope
  exact (T.average_field_sq_le k).trans ((tree_base_moment_le T hT).trans
    (pow_le_pow_right₀ (by linarith) (by omega)))

/-- Single-sign derivative energies have an additional factor of one over n. -/
theorem average_field_partial_sq_le_envelope (T : RootedTree) (k : ZMod n) (b : InversionClass n)
    {D : ℕ} (hT : T.nodeCount ≤ D) :
    average (fun x ↦ walshPartial (T.fieldCoefficient k) b x ^ 2) ≤ treeMomentEnvelope D / n := by
  have hDn : 0 < D := T.nodeCount_pos.trans_le hT
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDn
  have hT' : (T.nodeCount : ℝ) ≤ D := by exact_mod_cast hT
  apply (T.average_field_partial_sq_le k b).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold treeMomentEnvelope
  calc
    _ ≤ (2 * (D : ℝ))^D * (2 * (D : ℝ)) :=
      mul_le_mul (tree_base_moment_le T hT) (by linarith) (by positivity) (by positivity)
    _ = (2 * (D : ℝ))^(D+1) := (pow_succ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)

/-- The variance estimate for the derivative pairing has the manuscript's
one-over-n rate under the same size envelope. -/
theorem average_centered_treeDerivativePairing_sq_le_envelope (T S : RootedTree)
    (k j : ZMod n) {D : ℕ} (hT : T.nodeCount ≤ D) (hS : S.nodeCount ≤ D) :
    average (fun x ↦ (normalizedTreeDerivativePairing T S k j x -
      average (normalizedTreeDerivativePairing T S k j)) ^ 2) ≤ treeMomentEnvelope D / n := by
  have hDn : 0 < D := T.nodeCount_pos.trans_le hT
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDn
  let z := 2 * (D : ℝ)
  have hz : (2 : ℝ) ≤ z := by dsimp [z]; linarith
  have hz₁ : 1 ≤ z := by linarith
  have hZ₂ : (4 : ℝ) ≤ z^2 := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hz 2
  apply (average_centered_treeDerivativePairing_sq_le T S k j).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold treeMomentEnvelope
  calc
    _ ≤ 4 * z^(10*D+2) := by
      linarith only [unmatchedDerivativeConstant_le T S hT hS, unmatchedDerivativeConstant_le S T hS hT]
    _ ≤ z^2 * z^(10*D+2) := mul_le_mul_of_nonneg_right hZ₂ (by positivity)
    _ = z^(10*D+4) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := pow_le_pow_right₀ hz₁ (by omega)

end LovaszTheta.Circulant
