module

public import LovaszTheta.TreeLinearMoments

/-!
# Derivative moments for the Gaussian comparison

The variance of each normalized pairing bounds the centered part
of the weighted pairing. The first and second moment estimates
for the individual derivatives also bound the cubed flip weights.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n]
variable (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)

lemma comparisonGamma_treeCoefficients (x : InversionClass n → Bool) :
    comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k) x =
      ∑ i, ∑ j, (a i*a j) * normalizedTreeDerivativePairing (T i) (T j) (k i) (k j) x := by
  let p (i : I) (b : InversionClass n) := walshPartial ((T i).fieldCoefficient (k i)) b x
  have hTerm (b : InversionClass n) (i j : I) :
      ((a i / (T i).nodeCount) * p i b) * (a j * p j b) =
        ((a i*a j) / (T i).nodeCount) * (p i b * p j b) := by ring
  unfold comparisonGamma linearWalshPartial
  change (∑ b : InversionClass n, (∑ i, (a i/(T i).nodeCount) * p i b) * (∑ j, a j * p j b)) = _
  simp_rw [sum_mul, mul_sum, hTerm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← mul_sum]
  change ((a i*a j)/(T i).nodeCount) * (∑ b, p i b * p j b) =
    (a i*a j) * ((∑ b, p i b * p j b) / (T i).nodeCount)
  ring

private lemma l2Average_sum_pairing_le {Ω : Type*} [Fintype Ω]
    (p : I → I → Ω → ℝ) {C : ℝ} (h : ∀ i j, l2Average (p i j) ≤ C) :
    l2Average (fun x ↦ ∑ i, ∑ j, (a i*a j)*p i j x) ≤ (∑ i, |a i|)^2 * C := by
  calc
    _ ≤ ∑ i, ∑ j, l2Average (fun x ↦ (a i*a j)*p i j x) :=
      (l2Average_sum_le univ _).trans (sum_le_sum fun _ _ ↦ l2Average_sum_le univ _)
    _ ≤ ∑ i, ∑ j, (|a i| * |a j|)*C := by
      refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
      rw [l2Average_const_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i j) (by positivity)
    _ = _ := by simp only [← sum_mul, ← mul_sum, pow_two]

/-- The squared-mean estimate for the fluctuation of the derivative pairing. -/
theorem l2Average_centered_comparisonGamma_le {D : ℕ}
    (hD : ∀ i, (T i).nodeCount ≤ D) :
    let Γ := comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k)
    l2Average (fun x ↦ Γ x - average Γ) ≤
      (∑ i, |a i|)^2 * Real.sqrt (treeMomentEnvelope D / n) := by
  dsimp only
  change l2Average (fun x ↦ comparisonGamma a (fun i ↦ (T i).nodeCount)
    (treeCoefficients T k) x - average (fun y ↦
      comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k) y)) ≤ _
  simp_rw [comparisonGamma_treeCoefficients, average_sum, average_mul_left,
    ← sum_sub_distrib, ← mul_sub]
  apply l2Average_sum_pairing_le
  intro i j
  exact l2Average_le_of_average_sq_le
    (average_centered_treeDerivativePairing_sq_le_envelope (T i) (T j) (k i) (k j) (hD i) (hD j))

/-- The normalized pairing differs from the Gaussian variance by its
centered fluctuation and the covariance error. -/
theorem l2Average_comparisonGamma_sub_variance_le [Nonempty (InversionClass n)]
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j) :
    l2Average (fun x ↦ comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k) x -
      ∑ i, a i^2) ≤
      (∑ i, |a i|)^2 * (Real.sqrt (treeMomentEnvelope D / n) + treeMomentEnvelope D / Real.sqrt n) := by
  let Γ := comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k)
  let v := ∑ i, a i^2
  have hEq (x : InversionClass n → Bool) : Γ x-v = (Γ x-average Γ)+(average Γ-v) := by ring
  change l2Average (fun x ↦ Γ x-v) ≤ _
  simp_rw [hEq]
  rw [mul_add]
  refine (l2Average_add_le (fun x ↦ Γ x-average Γ) (fun _ ↦ average Γ-v)).trans
    (add_le_add (l2Average_centered_comparisonGamma_le a T k hD) ?_)
  have hm : average Γ = average (fun x ↦ linearWalsh a (treeCoefficients T k) x ^ 2) :=
    average_comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k)
      (fun i ↦ (T i).nodeCount_pos) (fun i _ h ↦ (T i).fieldCoefficient_eq_zero_of_card_ne (k i) h)
  apply (l2Average_const_le _).trans
  rw [hm]
  exact abs_average_linearWalsh_tree_sq_sub_le a T k hD hk hDistinct

/-- The aggregate squared single-coordinate derivative weights. -/
noncomputable def treeDelta (b : InversionClass n) : ℝ :=
  ∑ i, |a i| * l2Average (walshPartial ((T i).fieldCoefficient (k i)) b)

lemma treeDelta_nonneg (b : InversionClass n) : 0 ≤ treeDelta a T k b :=
  sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (l2Average_nonneg _)

lemma treeDelta_le {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (b : InversionClass n) :
    treeDelta a T k b ≤ (∑ i, |a i|) * Real.sqrt (treeMomentEnvelope D / n) := by
  unfold treeDelta
  rw [sum_mul]
  exact sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
    (l2Average_le_of_average_sq_le (average_field_partial_sq_le_envelope (T i) (k i) b (hD i)))
    (abs_nonneg _)

lemma sum_treePartial_energy (U : RootedTree) (j : ZMod n) :
    (∑ b, l2Average (walshPartial (U.fieldCoefficient j) b) ^ 2) =
      (U.nodeCount : ℝ) * average (fun x ↦ U.field x j ^ 2) := by
  simp_rw [l2Average_sq, sum_average_walshPartial_sq]
  have hm := average_walshCombination_mul (U.fieldCoefficient j) (U.fieldCoefficient j)
  simp_rw [← pow_two] at hm
  have he (x : InversionClass n → Bool) : U.field x j = walshCombination (U.fieldCoefficient j) x :=
    U.field_walsh_expansion x j
  simp_rw [he, hm]
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  by_cases h : s.card = U.nodeCount
  · simp [h, pow_two]
  · simp [U.fieldCoefficient_eq_zero_of_card_ne j h]

/-- The sum of the squared flip weights is bounded by the
degree-weighted second moments of the coordinates. -/
theorem sum_treeDelta_sq_le {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) :
    (∑ b, treeDelta a T k b ^ 2) ≤ (∑ i, |a i|)^2 * ((D : ℝ)*treeMomentEnvelope D) := by
  let p (i : I) (b : InversionClass n) := l2Average (walshPartial ((T i).fieldCoefficient (k i)) b)
  let M := (D : ℝ)*treeMomentEnvelope D
  have hM : 0 ≤ M := by unfold M treeMomentEnvelope; positivity
  have hEnergy (i : I) : (∑ b, p i b^2) ≤ M := by
    dsimp [p, M]
    rw [sum_treePartial_energy]
    exact mul_le_mul (by exact_mod_cast hD i) (average_field_sq_le_envelope (T i) (k i) (hD i))
      (average_sq_nonneg _) (by positivity)
  have hPair (i j : I) : (∑ b, p i b*p j b) ≤ M := by
    calc
      _ ≤ Real.sqrt (∑ b, p i b^2) * Real.sqrt (∑ b, p j b^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt univ (p i) (p j)
      _ ≤ Real.sqrt M * Real.sqrt M :=
        mul_le_mul (Real.sqrt_le_sqrt (hEnergy i)) (Real.sqrt_le_sqrt (hEnergy j))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hM
  have hSq (b : InversionClass n) : treeDelta a T k b^2 =
      ∑ i, ∑ j, (|a i| * |a j|)*(p i b*p j b) := by
    rw [treeDelta, pow_two, sum_mul]
    simp_rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by unfold p; ring
  simp_rw [hSq]
  rw [sum_comm]
  have hInner (i : I) : (∑ b, ∑ j, (|a i| * |a j|)*(p i b*p j b)) ≤
      ∑ j, (|a i| * |a j|)*M := by
    rw [sum_comm]
    simp_rw [← mul_sum]
    exact sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hPair i j) (by positivity)
  calc
    _ ≤ ∑ i, ∑ j, (|a i| * |a j|)*M := sum_le_sum fun i _ ↦ hInner i
    _ = _ := by simp only [← sum_mul, ← mul_sum, pow_two, M]

/-- One maximal flip weight times the sum of the squared weights
controls the third-order term. -/
theorem sum_treeDelta_cube_le {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) :
    (∑ b, treeDelta a T k b ^ 3) ≤
      ((∑ i, |a i|) * Real.sqrt (treeMomentEnvelope D / n)) *
        ((∑ i, |a i|)^2 * ((D : ℝ)*treeMomentEnvelope D)) := by
  let A := (∑ i, |a i|) * Real.sqrt (treeMomentEnvelope D / n)
  have hA : 0 ≤ A := by unfold A; positivity
  calc
    _ ≤ ∑ b, A * treeDelta a T k b^2 := by
      refine sum_le_sum fun b _ ↦ ?_
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right (treeDelta_le a T k hD b) (sq_nonneg _)
    _ = A * ∑ b, treeDelta a T k b^2 := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_treeDelta_sq_le a T k hD) hA

end LovaszTheta.Circulant
