module

public import LovaszTheta.FiniteMoments
public import LovaszTheta.GaussianMomentBounds

/-!
# Polynomial growth in the comparison estimates

The growth factors on a flip segment use the two endpoints.
Finite even moments bound the sign part, and the Gaussian
even moment bounds the independent Gaussian part.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LovaszTheta.Circulant

lemma abs_pow_even (x : ℝ) (r : ℕ) : |x|^(2*r) = x^(2*r) := by
  rw [pow_mul, sq_abs, ← pow_mul]

private lemma one_add_add_pow_le {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (p : ℕ) :
    (1+u+w)^p ≤ (3 : ℝ)^p * (1+u^p+w^p) := by
  let s := max 1 (max u w)
  have h₁ : 1 ≤ s := le_max_left _ _
  have h₂ : u ≤ s := (le_max_left u w).trans (le_max_right _ _)
  have h₃ : w ≤ s := (le_max_right u w).trans (le_max_right _ _)
  have hs : s^p ≤ 1+u^p+w^p := by
    rcases max_choice 1 (max u w) with h | h
    · change max 1 (max u w) = 1 at h
      unfold s
      rw [h, one_pow]
      linarith only [pow_nonneg hu p, pow_nonneg hw p]
    · unfold s
      rw [h]
      rcases max_choice u w with h' | h'
      · rw [h']
        linarith only [pow_nonneg hw p]
      · rw [h']
        linarith only [pow_nonneg hu p]
  calc
    _ ≤ (3*s)^p := pow_le_pow_left₀ (by positivity) (by linarith only [h₁, h₂, h₃]) _
    _ = (3 : ℝ)^p * s^p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- A bound for the sign contribution to the polynomial growth
factor, in terms of a common even moment of the two endpoints. -/
theorem l2Average_growth_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (V V' : Ω → ℝ) (r : ℕ) {L : ℝ}
    (hV : average (fun x ↦ V x^(2*r)) ≤ L) (hV' : average (fun x ↦ V' x^(2*r)) ≤ L) :
    l2Average (fun x ↦ (1+|V x|+|V' x|)^r) ≤ Real.sqrt ((3 : ℝ)^(2*r) * (1+L+L)) := by
  unfold l2Average
  apply Real.sqrt_le_sqrt
  have hp (x : Ω) : ((1+|V x|+|V' x|)^r)^2 ≤ (3 : ℝ)^(2*r) * (1+V x^(2*r)+V' x^(2*r)) := by
    rw [← pow_mul, Nat.mul_comm r 2, ← abs_pow_even (V x), ← abs_pow_even (V' x)]
    exact one_add_add_pow_le (abs_nonneg _) (abs_nonneg _) _
  refine (average_mono hp).trans ?_
  simp only [average_mul_left, average_add, average_const]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right hV _) hV') (by positivity)

/-- A bound for the Gaussian contribution to the polynomial growth factor. -/
noncomputable def comparisonGaussianGrowth (v : ℝ≥0) (r : ℕ) : ℝ :=
  (3 : ℝ)^r * (2 + ((2*r : ℝ) * (v : ℝ))^r)

lemma integrable_one_add_abs_pow_gaussian (v : ℝ≥0) (r : ℕ) :
    Integrable (fun g ↦ (1+|g|)^r) (gaussianReal 0 v) := by
  refine integrable_growth_gaussian v r 1 (by fun_prop) (fun g ↦ ?_)
  simp only [one_mul, abs_of_nonneg (by positivity : 0 ≤ (1+|g|)^r), le_rfl]

lemma integral_one_add_abs_pow_gaussian_le (v : ℝ≥0) (r : ℕ) :
    (∫ g, (1+|g|)^r ∂gaussianReal 0 v) ≤ comparisonGaussianGrowth v r := by
  have hg (x : ℝ) : |x|^r ≤ 1+|x|^(2*r) := by
    by_cases h : |x| ≤ 1
    · exact (pow_le_one₀ (abs_nonneg x) h).trans
        (le_add_of_nonneg_right (pow_nonneg (abs_nonneg x) _))
    · exact (pow_le_pow_right₀ (le_of_not_ge h) (by omega)).trans (le_add_of_nonneg_left zero_le_one)
  have hPoint (g : ℝ) : (1+|g|)^r ≤ (3 : ℝ)^r * (2+|g|^(2*r)) := by
    have he := one_add_add_pow_le (abs_nonneg g) (by norm_num : (0 : ℝ) ≤ 0) r
    by_cases h : r = 0
    · simp [h]
    · simp only [add_zero, zero_pow h] at he
      exact he.trans (mul_le_mul_of_nonneg_left (by linarith only [hg g]) (by positivity))
  have hIn : Integrable (fun g : ℝ ↦ |g|^(2*r)) (gaussianReal 0 v) := by
    convert (integrable_one_add_abs_pow_gaussian v (2*r)).mono'
      (f := fun g : ℝ ↦ |g|^(2*r)) (by fun_prop) (ae_of_all _ fun g ↦ ?_) using 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg g) (by linarith) _
  have hm := integral_mono (integrable_one_add_abs_pow_gaussian v r)
    ((integrable_const (2 : ℝ)).add hIn |>.const_mul ((3 : ℝ)^r)) hPoint
  rw [integral_const_mul] at hm
  change _ ≤ (3 : ℝ)^r * (∫ g, 2+|g|^(2*r) ∂gaussianReal 0 v) at hm
  rw [integral_add (integrable_const _) hIn, integral_const] at hm
  have hμ : (gaussianReal 0 v).real Set.univ = 1 := by simp [Measure.real]
  simp only [hμ, smul_eq_mul, one_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (integral_abs_pow_gaussian_le v r) _) (by positivity))

end LovaszTheta.Circulant
