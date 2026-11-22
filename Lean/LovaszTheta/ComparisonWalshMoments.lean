module

public import LovaszTheta.ComparisonDerivatives
public import LovaszTheta.Hypercontractive

/-!
# Even moments of the sums in the comparison

Both the linear combination and its sign derivatives are Walsh
polynomials of degree at most the bound for the original trees.
Their even moments follow from hypercontractivity.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

section Walsh

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq B]

/-- Coefficient of a support after removing a differentiated sign. -/
noncomputable def partialCoefficient (c : Finset B → ℝ) (b : B) (s : Finset B) : ℝ :=
  if b ∉ s then c (insert b s) else 0

lemma walshPartial_eq_walshCombination (c : Finset B → ℝ) (b : B) (x : B → Bool) :
    walshPartial c b x = walshCombination (partialCoefficient c b) x := by
  unfold walshPartial walshCombination partialCoefficient
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, ← sum_filter]
  refine sum_bij (fun s _ ↦ s.erase b) ?_ ?_ ?_ ?_
  · intro s _
    simp
  · intro s hs t ht h
    have hs' := (mem_filter.mp hs).2
    have ht' := (mem_filter.mp ht).2
    simpa only [insert_erase hs', insert_erase ht'] using congrArg (insert b) h
  · intro s hs
    have hs' := (mem_filter.mp hs).2
    exact ⟨insert b s, mem_filter.mpr ⟨mem_univ _, mem_insert_self _ _⟩, erase_insert hs'⟩
  · intro s hs
    rw [insert_erase (mem_filter.mp hs).2]

omit [DecidableEq B] in
lemma walshCombination_sum_coefficients (a : I → ℝ) (c : I → Finset B → ℝ) (x : B → Bool) :
    walshCombination (fun s ↦ ∑ i, a i * c i s) x = linearWalsh a c x := by
  simp only [walshCombination, linearWalsh, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ mul_assoc _ _ _

lemma linearWalshPartial_eq_walshCombination (a : I → ℝ) (c : I → Finset B → ℝ)
    (b : B) (x : B → Bool) :
    linearWalshPartial a c b x =
      walshCombination (fun s ↦ ∑ i, a i * partialCoefficient (c i) b s) x := by
  rw [walshCombination_sum_coefficients, linearWalshPartial, linearWalsh]
  simp_rw [walshPartial_eq_walshCombination]

end Walsh

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

omit [Fintype I] in
lemma treeCoefficients_eq_zero_of_degree_gt (T : I → RootedTree) (k : I → ZMod n) {D : ℕ}
    (hD : ∀ i, (T i).nodeCount ≤ D) (i : I) (s : Finset (InversionClass n)) (hs : D < s.card) :
    treeCoefficients T k i s = 0 :=
  (T i).fieldCoefficient_eq_zero_of_card_ne (k i) ((lt_of_le_of_lt (hD i) hs).ne')

/-- Hypercontractivity bounds the moments of any linear combination
of the tree coordinates at arbitrary frequencies. -/
theorem average_linearWalsh_tree_even_pow_le {m : ℕ} (hm : 0 < m)
    (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n) {D : ℕ}
    (hD : ∀ i, (T i).nodeCount ≤ D) :
    average (fun x ↦ linearWalsh a (treeCoefficients T k) x ^ (2*m)) ≤
      ((((2*m-1 : ℕ) : ℝ)^D) * (∑ i, |a i|)^2 * treeMomentEnvelope D)^m := by
  have hSupport (s : Finset (InversionClass n)) (hs : D < s.card) :
      (∑ i, a i * treeCoefficients T k i s) = 0 := by
    simp [treeCoefficients_eq_zero_of_degree_gt T k hD _ s hs]
  have h := average_even_pow_walshCombination_le hm (fun s ↦ ∑ i, a i * treeCoefficients T k i s) D hSupport
  simp_rw [walshCombination_sum_coefficients] at h
  apply h.trans
  rw [mul_assoc]
  exact pow_le_pow_left₀ (mul_nonneg (by positivity) (average_sq_nonneg _))
    (mul_le_mul_of_nonneg_left (average_linearWalsh_tree_sq_le a T k hD) (by positivity)) m

/-- The L2 norm of the derivative of a combination is bounded by the
sum of the weighted coordinate derivative norms. -/
lemma l2Average_linearWalshPartial_tree_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    (b : InversionClass n) :
    l2Average (linearWalshPartial a (treeCoefficients T k) b) ≤ treeDelta a T k b := by
  change l2Average (fun x ↦ ∑ i, a i * walshPartial ((T i).fieldCoefficient (k i)) b x) ≤ _
  refine (l2Average_sum_le univ _).trans ?_
  simp_rw [l2Average_const_mul]
  rfl

/-- Removing the sign leaves a polynomial of bounded degree. The
sixth moment uses the factor five from hypercontractivity. -/
theorem average_linearWalshPartial_tree_six_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (b : InversionClass n) :
    average (fun x ↦ linearWalshPartial a (treeCoefficients T k) b x ^ 6) ≤
      ((5 : ℝ)^D * treeDelta a T k b ^ 2)^3 := by
  let c (s : Finset (InversionClass n)) := ∑ i, a i * partialCoefficient (treeCoefficients T k i) b s
  have hSupport (s : Finset (InversionClass n)) (hs : D < s.card) : c s = 0 := by
    have hi : D < (insert b s).card := hs.trans_le (card_le_card (subset_insert _ _))
    simp [c, partialCoefficient, treeCoefficients_eq_zero_of_degree_gt T k hD _ _ hi]
  have h := average_even_pow_walshCombination_le (by decide : 0 < (3 : ℕ)) c D hSupport
  simp only [show 2 * 3 - 1 = (5 : ℕ) by decide, show 2 * 3 = (6 : ℕ) by decide, Nat.cast_ofNat] at h
  simp_rw [linearWalshPartial_eq_walshCombination]
  change average (fun x ↦ walshCombination c x ^ 6) ≤ _
  apply h.trans
  have hL := l2Average_linearWalshPartial_tree_le a T k b
  have hP := pow_le_pow_left₀ (l2Average_nonneg _) hL 2
  rw [l2Average_sq] at hP
  simp_rw [linearWalshPartial_eq_walshCombination] at hP
  apply pow_le_pow_left₀
  · exact mul_nonneg (by positivity) (average_sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left hP (by positivity)

/-- The sixth moment of the difference at a flip is the derivative
moment multiplied by the sixth power of two. -/
theorem average_flip_linearWalsh_tree_six_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (b : InversionClass n) :
    average (fun x ↦ (linearWalsh a (treeCoefficients T k) (flip b x) -
      linearWalsh a (treeCoefficients T k) x)^6) ≤
      (2 * Real.sqrt ((5 : ℝ)^D) * treeDelta a T k b)^6 := by
  have hSign (u : Bool) : sign u ^ 6 = 1 := by cases u <;> norm_num [sign]
  have hPoint (x : InversionClass n → Bool) :
      (linearWalsh a (treeCoefficients T k) (flip b x) - linearWalsh a (treeCoefficients T k) x)^6 =
      (2 : ℝ)^6 * (linearWalshPartial a (treeCoefficients T k) b x)^6 := by
    rw [linearWalsh_flip_sub]
    simp only [mul_pow, hSign, mul_one]
    norm_num
  simp_rw [hPoint, average_mul_left]
  refine (mul_le_mul_of_nonneg_left (average_linearWalshPartial_tree_six_le a T k hD b)
    (by positivity : 0 ≤ (2 : ℝ)^6)).trans_eq ?_
  let H := Real.sqrt ((5 : ℝ)^D)
  let δ := treeDelta a T k b
  have hH : H^2 = (5 : ℝ)^D := Real.sq_sqrt (by positivity)
  calc
    _ = ((2*H*δ)^2)^3 := by rw [mul_pow (2*H), mul_pow (2 : ℝ), hH]; ring
    _ = _ := by rw [← pow_mul]

/-- Dividing each coordinate by its degree can only decrease the
aggregate bound for the corresponding flip. -/
lemma treeDelta_div_nodeCount_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    (b : InversionClass n) :
    treeDelta (fun i ↦ a i/(T i).nodeCount) T k b ≤ treeDelta a T k b := by
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (l2Average_nonneg _)
  have hi : (1 : ℝ) ≤ (T i).nodeCount := by exact_mod_cast (T i).nodeCount_pos
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T i).nodeCount)]
  exact div_le_self (abs_nonneg _) hi

end LovaszTheta.Circulant
