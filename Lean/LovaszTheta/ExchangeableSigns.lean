module

public import LovaszTheta.Signs

/-!
# The exchangeable sign flip

Homogeneous Walsh polynomials are eigenvectors of the average
single-coordinate flip. The flip identity and derivative energy
identity are the discrete steps of the Gaussian comparison.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multilinear derivative with respect to a fair-sign coordinate. -/
noncomputable def walshPartial (c : Finset ι → ℝ) (b : ι) (x : ι → Bool) : ℝ :=
  ∑ s : Finset ι, if b ∈ s then c s * walsh (s.erase b) x else 0

private def containsCoefficient (b : ι) (c : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  if b ∈ s then c s else 0

omit [Fintype ι] in
private lemma flip_flip (b : ι) (x : ι → Bool) : flip b (flip b x) = x := by
  funext i
  by_cases h : i = b
  · subst i
    simp only [flip_same, Bool.not_not]
  · rw [flip_other h, flip_other h]

omit [Fintype ι] in
private lemma walsh_eq_mul_erase (s : Finset ι) {b : ι} (hb : b ∈ s) (x : ι → Bool) :
    walsh s x = sign (x b) * walsh (s.erase b) x := by
  unfold walsh
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem hb, Finset.sdiff_singleton_eq_erase]

private lemma walshCombination_contains (c : Finset ι → ℝ) (b : ι) (x : ι → Bool) :
    walshCombination (containsCoefficient b c) x = sign (x b) * walshPartial c b x := by
  unfold walshCombination walshPartial
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  by_cases hb : b ∈ s
  · simp only [containsCoefficient, ite_eq_left hb, walsh_eq_mul_erase s hb x]
    ring
  · simp [containsCoefficient, hb]

/-- Flipping one sign changes exactly the monomials that contain it. -/
private lemma walshCombination_flip_sub (c : Finset ι → ℝ) (b : ι) (x : ι → Bool) :
    walshCombination c (flip b x) - walshCombination c x =
      -2 * walshCombination (containsCoefficient b c) x := by
  unfold walshCombination
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro s _
  by_cases hb : b ∈ s
  · simp only [walsh_flip, ite_eq_left hb, containsCoefficient]
    ring
  · simp [walsh_flip, containsCoefficient, hb]

/-- The difference at a sign flip is the corresponding derivative,
multiplied by minus twice the old sign. -/
lemma walshCombination_flip_sub_eq_partial (c : Finset ι → ℝ) (b : ι) (x : ι → Bool) :
    walshCombination c (flip b x) - walshCombination c x =
      (-2 * sign (x b)) * walshPartial c b x := by
  rw [walshCombination_flip_sub, walshCombination_contains, mul_assoc]

/-- The product of two derivatives pairs coefficients at the supports
that contain the differentiated coordinate. -/
lemma average_walshPartial_mul (c d : Finset ι → ℝ) (b : ι) :
    average (fun x ↦ walshPartial c b x * walshPartial d b x) =
      ∑ s : Finset ι, if b ∈ s then c s * d s else 0 := by
  have hEq (x : ι → Bool) : walshPartial c b x * walshPartial d b x =
      walshCombination (containsCoefficient b c) x *
        walshCombination (containsCoefficient b d) x := by
    rw [walshCombination_contains, walshCombination_contains, mul_mul_mul_comm, ← pow_two,
      sign_sq, one_mul]
  simp_rw [hEq, average_walshCombination_mul]
  exact sum_congr rfl fun s _ ↦ by
    by_cases hb : b ∈ s <;> simp [containsCoefficient, hb]

/-- The derivative square sums the squared coefficients of the containing supports. -/
lemma average_walshPartial_sq (c : Finset ι → ℝ) (b : ι) :
    average (fun x ↦ walshPartial c b x ^ 2) =
      ∑ s : Finset ι, if b ∈ s then c s ^ 2 else 0 := by
  simpa only [pow_two] using average_walshPartial_mul c c b

/-- Summing the derivative pairings weights each coefficient pair
by its common support size. -/
theorem sum_average_walshPartial_mul (c d : Finset ι → ℝ) :
    (∑ b : ι, average (fun x ↦ walshPartial c b x * walshPartial d b x)) =
      ∑ s : Finset ι, (s.card : ℝ) * (c s * d s) := by
  simp_rw [average_walshPartial_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  simp

/-- The sum of the derivative energies is the degree-weighted Walsh energy. -/
theorem sum_average_walshPartial_sq (c : Finset ι → ℝ) :
    (∑ b : ι, average (fun x ↦ walshPartial c b x ^ 2)) =
      ∑ s : Finset ι, (s.card : ℝ) * c s ^ 2 := by
  simpa only [pow_two] using sum_average_walshPartial_mul c c

/-- Normalizing the derivative pairing by the degree of the homogeneous
factor gives the original covariance. -/
theorem average_normalized_derivative_pairing (c d : Finset ι → ℝ) {k : ℕ} (hk : 0 < k)
    (hDegree : ∀ s, s.card ≠ k → c s = 0) :
    average (fun x ↦ (∑ b, walshPartial c b x * walshPartial d b x) / k) =
      average (fun x ↦ walshCombination c x * walshCombination d x) := by
  have hK : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hSum : (∑ s, (s.card : ℝ) * (c s * d s)) = (k : ℝ) * ∑ s, c s * d s := by
    rw [mul_sum]
    apply sum_congr rfl
    intro s _
    by_cases h : s.card = k
    · simp [h]
    · simp [hDegree s h]
  simp_rw [div_eq_inv_mul, average_mul_left, average_sum, sum_average_walshPartial_mul, hSum,
    ← mul_assoc, inv_mul_cancel₀ hK, one_mul, average_walshCombination_mul]

private lemma sum_flip_sub_of_homogeneous (c : Finset ι → ℝ) (d : ℕ)
    (hDegree : ∀ s, s.card ≠ d → c s = 0) (x : ι → Bool) :
    (∑ b, (walshCombination c (flip b x) - walshCombination c x)) =
      -2 * (d : ℝ) * walshCombination c x := by
  simp_rw [walshCombination_flip_sub]
  unfold walshCombination
  rw [← mul_sum, mul_assoc (-2 : ℝ)]
  refine congrArg (fun r : ℝ ↦ -2 * r) ?_
  rw [mul_sum]
  change (∑ b, ∑ s : Finset ι, containsCoefficient b c s * walsh s x) =
    ∑ s : Finset ι, (d : ℝ) * (c s * walsh s x)
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  have hSimple (b : ι) :
      containsCoefficient b c s * walsh s x = if b ∈ s then c s * walsh s x else 0 := by
    by_cases hb : b ∈ s <;> simp [containsCoefficient, hb]
  simp_rw [hSimple]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  by_cases hs : s.card = d
  · simp [hs]
  · simp [hDegree s hs]

private lemma average_flip_pair (Y g : (ι → Bool) → ℝ) (b : ι) :
    average (fun x ↦ (Y (flip b x) - Y x) * (g (flip b x) - g x)) =
      2 * average (fun x ↦ (Y x - Y (flip b x)) * g x) := by
  have hInvariant := average_equiv (flip b) (fun x ↦ (Y x - Y (flip b x)) * g x)
  simp_rw [flip_flip] at hInvariant
  have hPoint (x : ι → Bool) :
      (Y (flip b x) - Y x) * (g (flip b x) - g x) =
        (Y (flip b x) - Y x) * g (flip b x) + (Y x - Y (flip b x)) * g x := by ring
  simp_rw [hPoint, average_add]
  rw [hInvariant]
  ring

/-- The single-sign exchangeable-pair identity for a homogeneous Walsh coordinate. -/
theorem average_homogeneous_mul_test [Nonempty ι] (c : Finset ι → ℝ) {d : ℕ} (hd : 0 < d)
    (hDegree : ∀ s, s.card ≠ d → c s = 0) (g : (ι → Bool) → ℝ) :
    average (fun x ↦ walshCombination c x * g x) =
      (Fintype.card ι : ℝ) / (4 * d) *
        average (fun b : ι ↦ average (fun x ↦
          (walshCombination c (flip b x) - walshCombination c x) *
            (g (flip b x) - g x))) := by
  let Y := walshCombination c
  have hSum (x : ι → Bool) : (∑ b, (Y x - Y (flip b x)) * g x) =
      (2 * (d : ℝ)) * (Y x * g x) := by
    have hNeg (b : ι) : Y x - Y (flip b x) = -(Y (flip b x) - Y x) := by ring
    rw [← sum_mul]
    simp_rw [hNeg, sum_neg_distrib]
    rw [sum_flip_sub_of_homogeneous c d hDegree]
    ring
  have h : (∑ b : ι, average (fun x ↦ (Y (flip b x) - Y x) * (g (flip b x) - g x))) =
      (4 * (d : ℝ)) * average (fun x ↦ Y x * g x) := by
    simp_rw [average_flip_pair]
    rw [← mul_sum, ← average_sum]
    simp_rw [hSum, average_mul_left]
    ring
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change average (fun x ↦ Y x * g x) = (Fintype.card ι : ℝ) / (4 * d) *
    ((∑ b : ι, average (fun x ↦ (Y (flip b x) - Y x) * (g (flip b x) - g x))) / Fintype.card ι)
  rw [h]
  field_simp

end LovaszTheta
