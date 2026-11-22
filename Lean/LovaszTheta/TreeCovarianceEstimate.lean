module

public import LovaszTheta.CovarianceCharacters

/-!
# The covariance estimate for regular frequencies

This completes the tree-moments lemma by normalizing the exact
unrestricted covariance and bounding the discarded assignments.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

namespace RootedTree.Isomorphism

variable {S T : RootedTree}

lemma nodeCount_eq (e : S.Isomorphism T) : S.nodeCount = T.nodeCount := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.val

/-- The induced bijection on leaves. -/
noncomputable def leafEquiv (e : S.Isomorphism T) : S.Leaf ≃ T.Leaf := e.val.subtypeEquiv (by
  intro u
  constructor
  · intro hu v hv
    apply e.val.symm.injective
    rw [Equiv.symm_apply_apply]
    apply hu
    have he := e.symm.property.2 v
    change e.val.symm (T.parent v) = S.parent (e.val.symm v) at he
    rw [← he, hv, Equiv.symm_apply_apply]
  · intro hu v hv
    apply e.val.injective
    apply hu
    rw [← e.property.2, hv])

lemma leafCount_eq (e : S.Isomorphism T) : Fintype.card S.Leaf = Fintype.card T.Leaf :=
  Fintype.card_congr e.leafEquiv

lemma card_automorphism_eq (e : S.Isomorphism T) :
    Fintype.card S.Automorphism = Fintype.card T.Automorphism := by
  let E : S.Isomorphism T ≃ T.Isomorphism S :=
    { toFun := fun f ↦ f.symm
      invFun := fun f ↦ f.symm
      left_inv := fun f ↦ Subtype.ext f.val.symm_symm
      right_inv := fun f ↦ Subtype.ext f.val.symm_symm }
  rw [← RootedTree.card_isomorphism_eq_card_automorphism e.symm,
    ← RootedTree.card_isomorphism_eq_card_automorphism e, Fintype.card_congr E]

end RootedTree.Isomorphism

private lemma normalizer_mul_unrestricted (T S : RootedTree) (k j : ZMod n)
    (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) :
    (T.fieldNormalizer n * S.fieldNormalizer n) *
      ((n : ℝ)^Fintype.card T.Leaf * Fintype.card (S.Isomorphism T) *
        (if j = k ∨ j = -k then 1 else 0)) =
      (if Nonempty (S.Isomorphism T) ∧ (j = k ∨ j = -k) then 1 else 0) := by
  by_cases hI : Nonempty (S.Isomorphism T)
  · let e := Classical.choice hI
    have hN : 0 < (n : ℝ)^Fintype.card T.Leaf := by
      have := NeZero.ne n
      positivity
    have hA : 0 < (Fintype.card T.Automorphism : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := T.Automorphism)
    have h := congrArg₂ (· * ·) (Real.sq_sqrt hN.le) (Real.sq_sqrt hA.le)
    rw [← mul_pow] at h
    rw [RootedTree.fieldNormalizer, RootedTree.fieldNormalizer, hL, e.card_automorphism_eq,
      RootedTree.card_isomorphism_eq_card_automorphism e]
    rw [← sq, ← mul_assoc, ← h, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, one_mul]
    simp [hI]
  · let _ : IsEmpty (S.Isomorphism T) := not_nonempty_iff.mp hI
    simp [hI]

private lemma normalizers_mul_pow_sub_one_le (T S : RootedTree)
    (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) :
    T.fieldNormalizer n * S.fieldNormalizer n * (n : ℝ)^(Fintype.card T.Leaf-1) ≤
      1 / Real.sqrt n := by
  let t := T.fieldNormalizer n
  let s := S.fieldNormalizer n
  let l := Fintype.card T.Leaf
  have hl : 1 ≤ l := by
    obtain ⟨i, _⟩ := T.descendantLeaves_nonempty T.root
    let _ : Nonempty T.Leaf := ⟨i⟩
    exact Fintype.card_pos
  have hN₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hN : (0 : ℝ) < n := zero_lt_one.trans_le hN₁
  have hP : t*s*(n : ℝ)^l ≤ 1 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ (0 : ℕ)) zero_le_one
    rw [show (t*s*(n : ℝ)^l)^2 = (t^2*(n : ℝ)^l)*(s^2*(n : ℝ)^l) by ring, one_pow]
    have hS := S.fieldNormalizer_sq_mul (n := n)
    rw [hL] at hS
    simpa only [one_mul] using
      mul_le_mul (T.fieldNormalizer_sq_mul (n := n)) hS (by positivity) zero_le_one
  calc
    _ = (t*s*(n : ℝ)^l) / n := by
      symm
      apply (div_eq_iff (ne_of_gt hN)).mpr
      change t*s*(n : ℝ)^l = (t*s*(n : ℝ)^(l-1)) * n
      rw [mul_assoc (t*s), ← pow_succ, Nat.sub_add_cancel hl]
    _ ≤ 1 / (n : ℝ) := div_le_div_of_nonneg_right hP hN.le
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hN)
      exact (Real.sqrt_le_left hN.le).mpr (by nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hN₁)])

private lemma covarianceError_le_envelope (T S : RootedTree) {D : ℕ}
    (hT : T.nodeCount ≤ D) (hS : S.nodeCount ≤ D) : covarianceError T S ≤ treeMomentEnvelope D := by
  let z := 2 * (D : ℝ)
  let E := (2*T.nodeCount + 2*T.nodeCount^2 : ℕ)
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast T.nodeCount_pos.trans_le hT
  have hT' : (T.nodeCount : ℝ) ≤ D := by exact_mod_cast hT
  have hS' : (S.nodeCount : ℝ) ≤ D := by exact_mod_cast hS
  have hz : 2 ≤ z := by dsimp [z]; linarith
  have hz₁ : 1 ≤ z := by linarith
  have hz₂ : z ≤ z^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz₁) (show 0 ≤ z by linarith)]
  have hz₃ : z^2+z ≤ z^3 := by
    have hZZ := mul_le_mul_of_nonneg_right hz (show 0 ≤ z^2 by positivity)
    nlinarith only [hz₂, hZZ]
  have hE : (E : ℝ) ≤ z^2 := by
    unfold E z
    push_cast
    have hSq := pow_le_pow_left₀ (by positivity : 0 ≤ (T.nodeCount : ℝ)) hT' 2
    have hDsq := mul_nonneg (sub_nonneg.mpr hD) (show (0 : ℝ) ≤ D by positivity)
    nlinarith only [hT', hSq, hDsq]
  have hB : ((E + (S.nodeCount+1) : ℕ) : ℝ) ≤ z^3 := by
    push_cast
    refine le_trans (add_le_add hE ?_) hz₃
    dsimp [z]
    linarith
  have hPower : ((2*T.nodeCount : ℕ) : ℝ)^S.nodeCount ≤ z^D :=
    (pow_le_pow_left₀ (by positivity) (by unfold z; exact_mod_cast Nat.mul_le_mul_left 2 hT) _).trans
      (pow_le_pow_right₀ hz₁ hS)
  change (E : ℝ) * _ + _ * ((E + (S.nodeCount + 1) : ℕ) : ℝ) ≤ z^(14*D)
  have hE' := hE.trans (pow_le_pow_right₀ hz₁ (by omega : 2 ≤ 3))
  calc
    _ ≤ z^3 * z^D + z^D * z^3 := by
      exact add_le_add (mul_le_mul hE' (tree_base_moment_le S hS) (by positivity) (by positivity))
        (mul_le_mul hPower hB (by positivity) (by positivity))
    _ = 2 * z^(D+3) := by rw [mul_comm (z^3), ← pow_add, two_mul]
    _ ≤ z * z^(D+3) := mul_le_mul_of_nonneg_right hz (by positivity)
    _ = z^(D+4) := by rw [mul_comm z, ← pow_succ]
    _ ≤ z^(14*D) := by
      have hn : 0 < D := T.nodeCount_pos.trans_le hT
      exact pow_le_pow_right₀ hz₁ (by omega)

private theorem abs_average_field_mul_sub_indicator_same_leaves (T S : RootedTree) (k j : ZMod n)
    (hk : RegularFrequency k) (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) :
    |average (fun x ↦ T.field x k * S.field x j) -
      (if Nonempty (S.Isomorphism T) ∧ (j = k ∨ j = -k) then 1 else 0)| ≤
      covarianceError T S / Real.sqrt n := by
  let b := T.fieldNormalizer n * S.fieldNormalizer n
  have hb : 0 ≤ b := by unfold b RootedTree.fieldNormalizer; positivity
  rw [average_field_mul_eq_normalizers_mul, ← normalizer_mul_unrestricted T S k j hL,
    ← sum_unrestrictedContribution T S k j hk hL, ← mul_sub, abs_mul, abs_of_nonneg hb]
  change b * _ ≤ _
  calc
    _ ≤ b * (covarianceError T S * (n : ℝ)^(Fintype.card T.Leaf-1)) :=
      mul_le_mul_of_nonneg_left (abs_unnormalizedCovarianceSum_sub_unrestricted_le T S k j) hb
    _ = covarianceError T S * (b * (n : ℝ)^(Fintype.card T.Leaf-1)) := by ring
    _ ≤ covarianceError T S * (1 / Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (normalizers_mul_pow_sub_one_le T S hL)
        (by unfold covarianceError; positivity)
    _ = _ := by rw [← mul_div_assoc, mul_one]

/-- The standardized fields have covariance within the common moment
envelope of the rooted-isomorphism and frequency indicator. -/
theorem abs_average_field_mul_sub_indicator_le (T S : RootedTree) (k j : ZMod n)
    (hk : RegularFrequency k) {D : ℕ} (hT : T.nodeCount ≤ D) (hS : S.nodeCount ≤ D) :
    |average (fun x ↦ T.field x k * S.field x j) -
      (if Nonempty (S.Isomorphism T) ∧ (j = k ∨ j = -k) then 1 else 0)| ≤
      treeMomentEnvelope D / Real.sqrt n := by
  have hRoot (U : RootedTree) (hU : U.nodeCount ≤ D) :
      ((2*U.nodeCount : ℕ) : ℝ)^Fintype.card U.Leaf ≤ treeMomentEnvelope D := by
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast U.nodeCount_pos.trans_le hU
    exact (tree_base_moment_le U hU).trans (pow_le_pow_right₀ (by linarith) (by omega))
  by_cases hNodes : T.nodeCount = S.nodeCount
  · rcases lt_trichotomy (Fintype.card S.Leaf) (Fintype.card T.Leaf) with hL | hL | hL
    · have hI : ¬ Nonempty (S.Isomorphism T) := fun ⟨e⟩ ↦ hL.ne e.leafCount_eq
      rw [ite_eq_right (fun h ↦ hI h.1), sub_zero]
      simp_rw [mul_comm (T.field _ k)]
      exact (abs_average_field_mul_le_of_leafCount_lt S T j k hL).trans
        (div_le_div_of_nonneg_right (hRoot T hT) (Real.sqrt_nonneg _))
    · exact (abs_average_field_mul_sub_indicator_same_leaves T S k j hk hL).trans
        (div_le_div_of_nonneg_right (covarianceError_le_envelope T S hT hS) (Real.sqrt_nonneg _))
    · have hI : ¬ Nonempty (S.Isomorphism T) := fun ⟨e⟩ ↦ hL.ne e.leafCount_eq.symm
      rw [ite_eq_right (fun h ↦ hI h.1), sub_zero]
      exact (abs_average_field_mul_le_of_leafCount_lt T S k j hL).trans
        (div_le_div_of_nonneg_right (hRoot S hS) (Real.sqrt_nonneg _))
  · have hI : ¬ Nonempty (S.Isomorphism T) := fun ⟨e⟩ ↦ hNodes e.nodeCount_eq.symm
    rw [ite_eq_right (fun h ↦ hI h.1), average_field_mul_eq_zero_of_nodeCount_ne T S k j hNodes,
      sub_zero, abs_zero]
    unfold treeMomentEnvelope
    positivity

end LovaszTheta.Circulant
