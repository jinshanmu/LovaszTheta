module

public import LovaszTheta.ComparisonFlip
public import LovaszTheta.FiniteMoments
public import LovaszTheta.TreeCovarianceEstimate

/-!
# Moments of linear combinations of tree fields

The leading covariance of distinct tree and frequency coordinates is
the identity. Summing the errors uses the coefficient `ℓ₁` norm.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

/-- The Walsh coefficients of a finite family of tree coordinates. -/
noncomputable def treeCoefficients (T : I → RootedTree) (k : I → ZMod n) :
    I → Finset (InversionClass n) → ℝ :=
  fun i ↦ (T i).fieldCoefficient (k i)

lemma linearWalsh_treeCoefficients (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    (x : InversionClass n → Bool) :
    linearWalsh a (treeCoefficients T k) x = ∑ i, a i * (T i).field x (k i) := by
  simp only [linearWalsh, treeCoefficients, walshCombination, RootedTree.field_walsh_expansion]

lemma abs_sum_pairing_le (a : I → ℝ) (p : I → I → ℝ) {C : ℝ} (h : ∀ i j, |p i j| ≤ C) :
    |∑ i, ∑ j, (a i*a j)*p i j| ≤ (∑ i, |a i|)^2 * C := by
  calc
    _ ≤ ∑ i, ∑ j, |(a i*a j)*p i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (|a i| * |a j|)*C := by
      refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i j) (by positivity)
    _ = _ := by simp only [← sum_mul, ← mul_sum, pow_two]

lemma average_linearWalsh_tree_sq (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n) :
    average (fun x ↦ linearWalsh a (treeCoefficients T k) x ^ 2) =
      ∑ i, ∑ j, (a i*a j)*average (fun x ↦ (T i).field x (k i) * (T j).field x (k j)) := by
  have hPoint (x : InversionClass n → Bool) :
      linearWalsh a (treeCoefficients T k) x ^ 2 =
        ∑ i, ∑ j, (a i*a j)*((T i).field x (k i) * (T j).field x (k j)) := by
    rw [linearWalsh_treeCoefficients, pow_two, sum_mul]
    simp_rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  simp_rw [hPoint, average_sum, average_mul_left]

lemma abs_average_treeField_mul_le_envelope (T S : RootedTree) (k j : ZMod n) {D : ℕ}
    (hT : T.nodeCount ≤ D) (hS : S.nodeCount ≤ D) :
    |average (fun x ↦ T.field x k * S.field x j)| ≤ treeMomentEnvelope D := by
  calc
    _ ≤ l2Average (fun x ↦ T.field x k) * l2Average (fun x ↦ S.field x j) :=
      abs_average_mul_le_l2Average _ _
    _ ≤ Real.sqrt (treeMomentEnvelope D) * Real.sqrt (treeMomentEnvelope D) :=
      mul_le_mul (l2Average_le_of_average_sq_le (average_field_sq_le_envelope T k hT))
        (l2Average_le_of_average_sq_le (average_field_sq_le_envelope S j hS))
        (l2Average_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (by unfold treeMomentEnvelope; positivity)

/-- The second moment at any frequencies is bounded by the envelope
times the squared coefficient sum. -/
theorem average_linearWalsh_tree_sq_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) :
    average (fun x ↦ linearWalsh a (treeCoefficients T k) x ^ 2) ≤
      (∑ i, |a i|)^2 * treeMomentEnvelope D := by
  rw [average_linearWalsh_tree_sq]
  exact (le_abs_self _).trans (abs_sum_pairing_le a _ fun i j ↦
    abs_average_treeField_mul_le_envelope (T i) (T j) (k i) (k j) (hD i) (hD j))

/-- The diagonal covariance for a family with no repeated tree and
frequency coordinates, up to frequency inversion. -/
theorem abs_average_linearWalsh_tree_sq_sub_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j) :
    |average (fun x ↦ linearWalsh a (treeCoefficients T k) x ^ 2) - ∑ i, a i^2| ≤
      (∑ i, |a i|)^2 * (treeMomentEnvelope D / Real.sqrt n) := by
  let q (i j : I) : ℝ := if i = j then 1 else 0
  have hQ : (∑ i, ∑ j, (a i*a j)*q i j) = ∑ i, a i^2 := by
    apply sum_congr rfl
    intro i _
    simp [q, mul_ite, pow_two]
  have hIndicator (i j : I) :
      ((if Nonempty ((T j).Isomorphism (T i)) ∧ (k j = k i ∨ k j = -k i) then 1 else 0) : ℝ) = q i j := by
    by_cases h : i = j
    · subst j
      have hIso : Nonempty ((T i).Isomorphism (T i)) :=
        ⟨⟨Equiv.refl _, rfl, fun _ ↦ rfl⟩⟩
      simp [q, hIso]
    · have he : ¬ (Nonempty ((T j).Isomorphism (T i)) ∧ (k j = k i ∨ k j = -k i)) :=
        fun hp ↦ h (hDistinct i j hp.1 hp.2)
      simp only [q, ite_eq_right he, ite_eq_right h]
  rw [average_linearWalsh_tree_sq, ← hQ]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  exact abs_sum_pairing_le a _ fun i j ↦ by
    rw [← hIndicator i j]
    exact abs_average_field_mul_sub_indicator_le (T i) (T j) (k i) (k j) (hk i) (hD i) (hD j)

lemma sq_sum_abs_le_card_mul_sq (a : I → ℝ) :
    (∑ i, |a i|)^2 ≤ (Fintype.card I : ℝ) * ∑ i, a i^2 := by
  simpa only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] using
    sum_mul_sq_le_sq_mul_sq (univ : Finset I) (fun _ ↦ (1 : ℝ)) (fun i ↦ |a i|)

/-- There are at most two frequencies excluded by the regularity condition. -/
theorem card_not_regularFrequency_le :
    Fintype.card {k : ZMod n // ¬RegularFrequency k} ≤ 2 := by
  have h := card_intCast_mul_fibre_le (n := n) (a := (2 : ℤ)) (by decide) 0
  simpa only [RegularFrequency, not_ne_iff, Int.cast_ofNat, show (2 : ℤ).natAbs = 2 by rfl] using h

end LovaszTheta.Circulant
