module

public import LovaszTheta.ComparisonGrowth
public import LovaszTheta.ComparisonHolder
public import LovaszTheta.ComparisonTaylor
public import LovaszTheta.GaussianInterpolation

/-!
# Bounds for the interpolated flip remainder

For a fixed Gaussian sample, the sign average uses three sixth
moments and the second moment of the segment's growth factor.
-/

@[expose] public section

open Set

namespace LovaszTheta.Circulant

variable {Ω : Type*}

/-- The difference of a coordinate at an update and at the original assignment. -/
def updateDifference (s : Ω → Ω) (V : Ω → ℝ) (x : Ω) : ℝ := V (s x)-V x

/-- The term multiplying the third derivative in the flip identity. -/
noncomputable def comparisonRemainder (s : Ω → Ω) (V W : Ω → ℝ)
    (f f' : ℝ → ℝ) (t g : ℝ) (x : Ω) : ℝ :=
  let u := gaussianBlend t (V x) g
  let u' := gaussianBlend t (V (s x)) g
  updateDifference s W x * (f u' - f u - (Real.sqrt t * f' u)*updateDifference s V x)

private lemma abs_comparisonRemainder_le (s : Ω → Ω) (V W : Ω → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    (hGrow : ∀ y, |iteratedDeriv 2 f y| ≤ C*(1+|y|)^r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (g : ℝ) (x : Ω) :
    |comparisonRemainder s V W f (deriv f) t g x| ≤
      ((C/2)*t*(1+|g|)^r) *
        (|updateDifference s W x| * |updateDifference s V x|^2 *
          (1+|V x|+|V (s x)|)^r) := by
  let u := gaussianBlend t (V x) g
  let u' := gaussianBlend t (V (s x)) g
  have hDiff : u'-u = Real.sqrt t*updateDifference s V x := by
    unfold u u' gaussianBlend updateDifference
    ring
  have hD : deriv f u * (u'-u) = (Real.sqrt t * deriv f u) * updateDifference s V x := by
    rw [hDiff]
    ring
  have hMax : 1+max |u| |u'| ≤ (1+|V x|+|V (s x)|)*(1+|g|) := by
    have hLeft : 1+|u| ≤ (1+|V x|+|V (s x)|)*(1+|g|) :=
      (one_add_abs_gaussianBlend_le ht (V x) g).trans (
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (V (s x))]) (by positivity : 0 ≤ 1+|g|))
    have hRight : 1+|u'| ≤ (1+|V x|+|V (s x)|)*(1+|g|) :=
      (one_add_abs_gaussianBlend_le ht (V (s x)) g).trans (
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (V x)]) (by positivity : 0 ≤ 1+|g|))
    rcases max_choice |u| |u'| with h | h
    · rw [h]
      exact hLeft
    · rw [h]
      exact hRight
  change |updateDifference s W x * (f u' - f u -
    (Real.sqrt t * deriv f u) * updateDifference s V x)| ≤ _
  rw [← hD, abs_mul]
  calc
    _ ≤ |updateDifference s W x| * ((C/2)*|u'-u|^2*(1+max |u| |u'|)^r) :=
      mul_le_mul_of_nonneg_left (abs_taylor_remainder_le hf r C hC hGrow u u') (abs_nonneg _)
    _ ≤ |updateDifference s W x| *
        ((C/2)*|u'-u|^2*((1+|V x|+|V (s x)|)*(1+|g|))^r) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMax _) (by positivity))
        (abs_nonneg _)
    _ = _ := by
      rw [hDiff, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt ht.1, mul_pow]
      ring

variable [Fintype Ω] [Nonempty Ω]

/-- The Taylor term has the comparison remainder bound after the one-sign
average, for a fixed Gaussian sample. -/
theorem abs_average_comparisonRemainder_le (s : Ω → Ω) (V W : Ω → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    (hGrow : ∀ y, |iteratedDeriv 2 f y| ≤ C*(1+|y|)^r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (g : ℝ) (A B X : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : average (fun x ↦ updateDifference s W x ^ 6) ≤ A^6)
    (hV : average (fun x ↦ updateDifference s V x ^ 6) ≤ B^6)
    (hX : l2Average (fun x ↦ (1+|V x|+|V (s x)|)^r) ≤ X) :
    |average (comparisonRemainder s V W f (deriv f) t g)| ≤
      ((C/2)*t*(1+|g|)^r) * (A*B^2*X) := by
  let K := (C/2)*t*(1+|g|)^r
  let G (x : Ω) := (1+|V x|+|V (s x)|)^r
  have hK : 0 ≤ K := by have := ht.1; unfold K; positivity
  have hHolder := average_abs_mul_sq_mul_le_of_six (updateDifference s W) (updateDifference s V) G hA hB hW hV
  have hGn (x : Ω) : 0 ≤ G x := by unfold G; positivity
  simp only [abs_of_nonneg (hGn _)] at hHolder
  apply (abs_average_le_average_abs _).trans
  apply (average_mono (abs_comparisonRemainder_le s V W hf C r hC hGrow ht g)).trans
  rw [average_mul_left]
  exact mul_le_mul_of_nonneg_left
    (hHolder.trans (mul_le_mul_of_nonneg_left hX (by positivity))) hK

omit [Nonempty Ω] in
/-- The covariance term uses the second moment of the pairing error
and the second moment of the growth factor. -/
theorem abs_average_comparison_covariance_le (U V : Ω → ℝ) {f : ℝ → ℝ}
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C) (hf : ∀ y, |f y| ≤ C*(1+|y|)^r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (g : ℝ) :
    |average (fun x ↦ U x * f (gaussianBlend t (V x) g))| ≤
      (C*(1+|g|)^r) * (l2Average U * l2Average (fun x ↦ (1+|V x|)^r)) := by
  let A := C*(1+|g|)^r
  let B (x : Ω) := (1+|V x|)^r
  have hBound (x : Ω) : |f (gaussianBlend t (V x) g)| ≤ A*B x := by
    calc
      _ ≤ C*(1+|gaussianBlend t (V x) g|)^r := hf _
      _ ≤ C*((1+|V x|)*(1+|g|))^r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (one_add_abs_gaussianBlend_le ht _ _) _) hC
      _ = _ := by unfold A B; rw [mul_pow]; ring
  have hPt (x : Ω) :
      |U x * f (gaussianBlend t (V x) g)| ≤ A * |U x * B x| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ B x by unfold B; positivity)]
    exact (mul_le_mul_of_nonneg_left (hBound x) (abs_nonneg _)).trans_eq (by ring)
  refine (abs_average_le_average_abs _).trans ((average_mono hPt).trans ?_)
  rw [average_mul_left]
  exact mul_le_mul_of_nonneg_left (average_abs_mul_le_l2Average U B) (by unfold A; positivity)

end LovaszTheta.Circulant
