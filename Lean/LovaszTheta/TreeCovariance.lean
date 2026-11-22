module

public import LovaszTheta.TreeMomentEnvelope

/-!
# Covariance of tree coordinates with different sizes

Walsh orthogonality requires a complete match of the sign supports.
For different leaf counts, choosing the smaller leaf assignment
first gives the extra inverse square root of the modulus.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma field_eq_sum_assignmentWeights (T : RootedTree) (k : ZMod n)
    (x : InversionClass n → Bool) :
    T.field x k = ∑ a : T.Assignment n, assignmentWeight T k a * walsh (T.signSupport a) x := by
  simp only [RootedTree.field_eq_sum, assignmentWeight, mul_sum, mul_assoc]

/-- Only pairs of assignments with identical sign supports contribute
to the covariance. -/
theorem average_field_mul_eq_sum_matches (T S : RootedTree) (k j : ZMod n) :
    average (fun x ↦ T.field x k * S.field x j) =
      ∑ a : T.Assignment n, ∑ b : S.Assignment n,
        if S.signSupport b = T.signSupport a then assignmentWeight T k a * assignmentWeight S j b else 0 := by
  have hTerm (a : T.Assignment n) (b : S.Assignment n) (x : InversionClass n → Bool) :
      (assignmentWeight T k a * walsh (T.signSupport a) x) *
        (assignmentWeight S j b * walsh (S.signSupport b) x) =
      (assignmentWeight T k a * assignmentWeight S j b) *
        (walsh (T.signSupport a) x * walsh (S.signSupport b) x) := by ring
  simp_rw [field_eq_sum_assignmentWeights, sum_mul, mul_sum, hTerm, average_sum,
    average_mul_left, average_walsh_mul, mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases h : T.signSupport a = S.signSupport b
  · simp [h]
  · simp [h, Ne.symm h]

/-- Coordinates of different node counts have zero covariance. -/
theorem average_field_mul_eq_zero_of_nodeCount_ne (T S : RootedTree) (k j : ZMod n)
    (h : T.nodeCount ≠ S.nodeCount) :
    average (fun x ↦ T.field x k * S.field x j) = 0 := by
  rw [average_field_mul_eq_sum_matches]
  have hNe (a : T.Assignment n) (b : S.Assignment n) : S.signSupport b ≠ T.signSupport a := by
    intro he
    apply h
    simpa only [RootedTree.signSupport_card] using congrArg Finset.card he.symm
  simp [hNe]

private lemma normalizers_mul_pow_le (T S : RootedTree)
    (hLeaf : Fintype.card T.Leaf < Fintype.card S.Leaf) :
    T.fieldNormalizer n * S.fieldNormalizer n * (n : ℝ)^Fintype.card T.Leaf ≤
      1 / Real.sqrt n := by
  let t := T.fieldNormalizer n
  let s := S.fieldNormalizer n
  let l := Fintype.card T.Leaf
  let l' := Fintype.card S.Leaf
  let N := (n : ℝ)
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hSqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have ht : 0 ≤ t := by unfold t RootedTree.fieldNormalizer; positivity
  have hs : 0 ≤ s := by unfold s RootedTree.fieldNormalizer; positivity
  have hPow : N^(2*l+1) ≤ N^(l+l') := pow_le_pow_right₀ hN (by
    change l < l' at hLeaf
    omega)
  change t*s*N^l ≤ 1 / Real.sqrt N
  apply (le_div_iff₀ hSqrt).mpr
  apply le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ (0 : ℕ)) zero_le_one
  calc
    _ = (t^2 * s^2) * N^(2*l+1) := by
      calc
        _ = (t^2 * s^2) * ((N^l)^2 * N) := by
          simp only [mul_pow, Real.sq_sqrt hNpos.le]
          ring
        _ = _ := by rw [← pow_mul N l 2, ← pow_succ, Nat.mul_comm l 2]
    _ ≤ (t^2 * s^2) * N^(l+l') := mul_le_mul_of_nonneg_left hPow (by positivity)
    _ = (t^2 * N^l) * (s^2 * N^l') := by rw [pow_add]; ring
    _ ≤ _ := by
      simpa only [one_pow, one_mul] using
        mul_le_mul (T.fieldNormalizer_sq_mul (n := n)) (S.fieldNormalizer_sq_mul (n := n))
          (by positivity) zero_le_one

/-- Choosing the smaller leaf assignment first bounds unequal-leaf
covariances at the inverse-square-root rate, at every frequency. -/
theorem abs_average_field_mul_le_of_leafCount_lt (T S : RootedTree) (k j : ZMod n)
    (hLeaf : Fintype.card T.Leaf < Fintype.card S.Leaf) :
    |average (fun x ↦ T.field x k * S.field x j)| ≤
      (((2*S.nodeCount : ℕ) : ℝ)^Fintype.card S.Leaf) / Real.sqrt n := by
  let t := T.fieldNormalizer n
  let s := S.fieldNormalizer n
  let C := (((2*S.nodeCount : ℕ) : ℝ)^Fintype.card S.Leaf)
  have ht : 0 ≤ t := by unfold t RootedTree.fieldNormalizer; positivity
  have hs : 0 ≤ s := by unfold s RootedTree.fieldNormalizer; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  have hWeight (a : T.Assignment n) (b : S.Assignment n) :
      |assignmentWeight T k a * assignmentWeight S j b| ≤ t*s := by
    rw [abs_mul]
    exact mul_le_mul (abs_assignmentWeight_le T k a) (abs_assignmentWeight_le S j b)
      (abs_nonneg _) ht
  have hPoint (a : T.Assignment n) :
      |∑ b : S.Assignment n, if S.signSupport b = T.signSupport a then
        assignmentWeight T k a * assignmentWeight S j b else 0| ≤ t*s*C := by
    let B := univ.filter (fun b : S.Assignment n ↦ S.signSupport b = T.signSupport a)
    rw [← sum_filter]
    have hCount : (B.card : ℝ) ≤ C := by
      have h := S.card_assignment_support_le (T.signSupport a)
      unfold C
      exact_mod_cast h
    calc
      _ ≤ ∑ b ∈ B, |assignmentWeight T k a * assignmentWeight S j b| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b ∈ B, t*s := sum_le_sum fun b _ ↦ hWeight a b
      _ = (t*s) * B.card := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hCount (mul_nonneg ht hs)
  have hN : (Fintype.card (T.Assignment n) : ℝ) ≤ (n : ℝ)^Fintype.card T.Leaf := by
    have h := Fintype.card_le_of_injective (fun a : T.Assignment n ↦ a.val) Subtype.val_injective
    rw [Fintype.card_fun, ZMod.card] at h
    exact_mod_cast h
  rw [average_field_mul_eq_sum_matches]
  calc
    _ ≤ ∑ _a : T.Assignment n, t*s*C :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ ↦ hPoint a)
    _ = (Fintype.card (T.Assignment n) : ℝ) * (t*s*C) := by simp
    _ ≤ (n : ℝ)^Fintype.card T.Leaf * (t*s*C) :=
      mul_le_mul_of_nonneg_right hN (mul_nonneg (mul_nonneg ht hs) hC)
    _ = C * (t*s*(n : ℝ)^Fintype.card T.Leaf) := by ring
    _ ≤ C * (1 / Real.sqrt n) := mul_le_mul_of_nonneg_left (normalizers_mul_pow_le T S hLeaf) hC
    _ = _ := by rw [← mul_div_assoc, mul_one]

end LovaszTheta.Circulant
