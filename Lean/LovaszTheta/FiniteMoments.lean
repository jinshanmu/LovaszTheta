module

public import LovaszTheta.Signs
public import Mathlib.Analysis.Real.Sqrt

/-!
# Finite mean-square inequalities

The estimates for a linear combination use Cauchy--Schwarz and the
triangle inequality with the normalization of the uniform average.
-/

@[expose] public section

open Finset

namespace LovaszTheta.Circulant

variable {Ω : Type*} [Fintype Ω]

lemma average_sq_nonneg (f : Ω → ℝ) :
    0 ≤ average (fun x ↦ f x ^ 2) :=
  div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)

lemma abs_average_le_average_abs (f : Ω → ℝ) :
    |average f| ≤ average (fun x ↦ |f x|) := by
  unfold average
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card Ω)]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (by positivity)

/-- The square root of the mean square on a finite space. -/
noncomputable def l2Average (f : Ω → ℝ) : ℝ :=
  Real.sqrt (average (fun x ↦ f x ^ 2))

lemma l2Average_nonneg (f : Ω → ℝ) : 0 ≤ l2Average f := Real.sqrt_nonneg _

lemma l2Average_sq (f : Ω → ℝ) : l2Average f ^ 2 = average (fun x ↦ f x ^ 2) :=
  Real.sq_sqrt (average_sq_nonneg f)

lemma average_abs_mul_le_l2Average (f g : Ω → ℝ) :
    average (fun x ↦ |f x * g x|) ≤ l2Average f * l2Average g := by
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (mul_nonneg (l2Average_nonneg _) (l2Average_nonneg _))
  rw [mul_pow, l2Average_sq, l2Average_sq]
  unfold average
  rw [div_pow, ← mul_div_mul_comm, ← pow_two (Fintype.card Ω : ℝ)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [← abs_mul, sq_abs] using sum_mul_sq_le_sq_mul_sq univ (fun x ↦ |f x|) (fun x ↦ |g x|)

lemma abs_average_mul_le_l2Average (f g : Ω → ℝ) :
    |average (fun x ↦ f x * g x)| ≤ l2Average f * l2Average g :=
  (abs_average_le_average_abs _).trans (average_abs_mul_le_l2Average f g)

lemma l2Average_add_le (f g : Ω → ℝ) :
    l2Average (fun x ↦ f x + g x) ≤ l2Average f + l2Average g := by
  have h := (le_abs_self _).trans (abs_average_mul_le_l2Average f g)
  have hSq (x : Ω) :
      (f x+g x)^2 = f x^2 + g x^2 + 2*(f x*g x) := by ring
  unfold l2Average
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  simp_rw [hSq, average_add, average_mul_left]
  change _ ≤ (l2Average f + l2Average g)^2
  nlinarith only [h, l2Average_sq f, l2Average_sq g]

lemma l2Average_const_mul (a : ℝ) (f : Ω → ℝ) :
    l2Average (fun x ↦ a * f x) = |a| * l2Average f := by
  simp_rw [l2Average, mul_pow, average_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma l2Average_const_le (a : ℝ) : l2Average (fun _ : Ω ↦ a) ≤ |a| := by
  cases isEmpty_or_nonempty Ω with
  | inl h => simp [l2Average, average, abs_nonneg]
  | inr h => simp [l2Average, Real.sqrt_sq_eq_abs]

lemma l2Average_sum_le {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    l2Average (fun x ↦ ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, l2Average (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2Average, average]
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (l2Average_add_le (f i) (fun x ↦ ∑ j ∈ s, f j x)).trans (add_le_add_right ih _)

lemma l2Average_le_of_average_sq_le {f : Ω → ℝ} {C : ℝ}
    (h : average (fun x ↦ f x ^ 2) ≤ C) : l2Average f ≤ Real.sqrt C :=
  Real.sqrt_le_sqrt h

end LovaszTheta.Circulant
