module

public import LovaszTheta.ExchangeableSigns

/-!
# The exchangeable-pair identity for a linear combination

The inverse degree in the flip identity weights the first derivative
in each pairing. The exact remainder keeps the two values of the
test function at the original and flipped assignments.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq B]

/-- A weighted sum of Walsh coordinates. -/
noncomputable def linearWalsh (a : I → ℝ) (c : I → Finset B → ℝ) (x : B → Bool) : ℝ :=
  ∑ i, a i * walshCombination (c i) x

/-- The multilinear derivative of the weighted sum. -/
noncomputable def linearWalshPartial (a : I → ℝ) (c : I → Finset B → ℝ)
    (b : B) (x : B → Bool) : ℝ :=
  ∑ i, a i * walshPartial (c i) b x

lemma linearWalsh_flip_sub (a : I → ℝ) (c : I → Finset B → ℝ) (b : B) (x : B → Bool) :
    linearWalsh a c (flip b x) - linearWalsh a c x =
      (-2*sign (x b)) * linearWalshPartial a c b x := by
  rw [linearWalsh, linearWalsh, ← sum_sub_distrib, linearWalshPartial, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← mul_sub, walshCombination_flip_sub_eq_partial]
  ring

/-- The derivative pairing `Γ` for the linear combination in the comparison. -/
noncomputable def comparisonGamma (a : I → ℝ) (d : I → ℕ) (c : I → Finset B → ℝ)
    (x : B → Bool) : ℝ :=
  ∑ b : B, linearWalshPartial (fun i ↦ a i / d i) c b x * linearWalshPartial a c b x

private lemma average_homogeneous_mul_test_sum [Nonempty B] (c : Finset B → ℝ) {d : ℕ}
    (hd : 0 < d) (hDegree : ∀ s, s.card ≠ d → c s = 0) (g : (B → Bool) → ℝ) :
    average (fun x ↦ walshCombination c x * g x) =
      (∑ b : B, average (fun x ↦ (walshCombination c (flip b x) - walshCombination c x) *
        (g (flip b x) - g x))) / (4*(d : ℝ)) := by
  rw [average_homogeneous_mul_test c hd hDegree g]
  let s (b : B) := average (fun x ↦ (walshCombination c (flip b x) - walshCombination c x) *
    (g (flip b x) - g x))
  change (Fintype.card B : ℝ) / (4*d) * ((∑ b : B, s b) / Fintype.card B) =
    (∑ b : B, s b) / (4*d)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

private lemma average_linear_mul_test [Nonempty B]
    (a : I → ℝ) (d : I → ℕ) (c : I → Finset B → ℝ)
    (hd : ∀ i, 0 < d i) (hDegree : ∀ i s, s.card ≠ d i → c i s = 0)
    (g : (B → Bool) → ℝ) :
    average (fun x ↦ linearWalsh a c x * g x) =
      (1/4) * ∑ b : B, average (fun x ↦
        (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
          (g (flip b x) - g x)) := by
  have hV (x : B → Bool) : linearWalsh a c x * g x =
      ∑ i, a i * (walshCombination (c i) x * g x) := by
    simp only [linearWalsh, sum_mul, mul_assoc]
  have hW (b : B) (x : B → Bool) :
      (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
        (g (flip b x) - g x) =
      ∑ i, (a i / d i) * ((walshCombination (c i) (flip b x) - walshCombination (c i) x) *
        (g (flip b x) - g x)) := by
    simp only [linearWalsh, ← sum_sub_distrib, sum_mul, ← mul_sub, mul_assoc]
  have hMean (i : I) := average_homogeneous_mul_test_sum (c i) (hd i) (hDegree i) g
  simp_rw [hV, hW, average_sum, average_mul_left, hMean]
  rw [sum_comm (γ := B), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum]
  ring

/-- The flip identity split into the linear Taylor term and the exact
remainder. The Gaussian coordinate can be fixed when applying this identity. -/
theorem average_linear_mul_test_sub_gamma [Nonempty B]
    (a : I → ℝ) (d : I → ℕ) (c : I → Finset B → ℝ)
    (hd : ∀ i, 0 < d i) (hDegree : ∀ i s, s.card ≠ d i → c i s = 0)
    (g h : (B → Bool) → ℝ) :
    average (fun x ↦ linearWalsh a c x * g x) -
      average (fun x ↦ comparisonGamma a d c x * h x) =
      (1/4) * ∑ b : B, average (fun x ↦
        (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
          (g (flip b x) - g x - h x*(linearWalsh a c (flip b x) - linearWalsh a c x))) := by
  rw [average_linear_mul_test a d c hd hDegree g]
  have hΓ (b : B) (x : B → Bool) :
      (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
        (h x*(linearWalsh a c (flip b x) - linearWalsh a c x)) =
      4 * ((linearWalshPartial (fun i ↦ a i / d i) c b x * linearWalshPartial a c b x) * h x) := by
    rw [linearWalsh_flip_sub, linearWalsh_flip_sub]
    have hSign := sign_sq (x b)
    linear_combination 4 * ((linearWalshPartial (fun i ↦ a i / d i) c b x *
      linearWalshPartial a c b x) * h x) * hSign
  have hDiff (b : B) (x : B → Bool) :
      (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
        (g (flip b x) - g x - h x*(linearWalsh a c (flip b x) - linearWalsh a c x)) =
      (linearWalsh (fun i ↦ a i / d i) c (flip b x) - linearWalsh (fun i ↦ a i / d i) c x) *
        (g (flip b x) - g x) -
      4 * ((linearWalshPartial (fun i ↦ a i / d i) c b x * linearWalshPartial a c b x) * h x) := by
    rw [mul_sub, hΓ]
  simp_rw [hDiff, average_sub, average_mul_left, sum_sub_distrib]
  simp only [comparisonGamma, sum_mul, average_sum, ← mul_sum]
  ring

/-- The mean derivative pairing is the second moment of the linear combination. -/
theorem average_comparisonGamma [Nonempty B]
    (a : I → ℝ) (d : I → ℕ) (c : I → Finset B → ℝ)
    (hd : ∀ i, 0 < d i) (hDegree : ∀ i s, s.card ≠ d i → c i s = 0) :
    average (comparisonGamma a d c) = average (fun x ↦ (linearWalsh a c x)^2) := by
  have h := average_linear_mul_test_sub_gamma a d c hd hDegree (linearWalsh a c) (fun _ ↦ 1)
  have he : average (fun x ↦ (linearWalsh a c x)^2) - average (comparisonGamma a d c) = 0 := by
    simpa [← pow_two] using h
  exact (sub_eq_zero.mp he).symm

end LovaszTheta.Circulant
