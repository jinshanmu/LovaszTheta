module

public import LovaszTheta.Barrier
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Data.Matrix.Mul

/-!
# Stability of the smoothed Fourier equation

The residual estimate uses the two positive barrier factors and a
self-adjoint linear operator whose square removes the constant vector.
The energy calculation is finite-dimensional.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix

namespace LovaszTheta.Circulant

variable {V : Type*} [Fintype V]

/-- The Euclidean norm with counting measure. -/
noncomputable def norm₂ (x : V → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

lemma norm₂_nonneg (x : V → ℝ) : 0 ≤ norm₂ x := Real.sqrt_nonneg _

lemma norm₂_sq (x : V → ℝ) : norm₂ x ^ 2 = x ⬝ᵥ x :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i))

lemma abs_dotProduct_le (x y : V → ℝ) : |x ⬝ᵥ y| ≤ norm₂ x * norm₂ y := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (norm₂_nonneg _) (norm₂_nonneg _))
  rw [mul_pow, norm₂_sq, norm₂_sq]
  simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq univ x y

/-- The orthogonal projection onto the constant vectors. -/
noncomputable def meanVector (x : V → ℝ) : V → ℝ :=
  fun _ ↦ mass x / Fintype.card V

private lemma dotProduct_meanVector (x y : V → ℝ) :
    x ⬝ᵥ meanVector y = mass x * mass y / Fintype.card V := by
  change (∑ i, x i * (mass y / Fintype.card V)) = _
  rw [← sum_mul, mul_div_assoc]
  rfl

/-- The smoothed activation with coordinate-dependent weights. -/
noncomputable def smooth (w v : V → ℝ) : V → ℝ :=
  fun i ↦ Real.sqrt ((v i) ^ 2 + 4 * w i)

/-- The positive factor constructed from a trial vector. -/
noncomputable def trialFactor (w v : V → ℝ) : V → ℝ :=
  fun i ↦ (smooth w v i + v i) / 2

private noncomputable def trialComplement (w v : V → ℝ) : V → ℝ :=
  fun i ↦ (smooth w v i - v i) / 2

omit [Fintype V] in
private lemma trialFactor_spec {w v : V → ℝ} (hw : ∀ i, 0 < w i) (i : V) :
    0 < trialFactor w v i ∧ 0 < trialComplement w v i ∧
    trialFactor w v i * trialComplement w v i = w i := by
  have hn : 0 ≤ v i ^ 2 + 4 * w i := add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (hw i).le)
  have hsq : smooth w v i ^ 2 = v i ^ 2 + 4 * w i := Real.sq_sqrt hn
  have habs : |v i| < smooth w v i := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    linarith [hw i]
  obtain ⟨h₁, h₂⟩ := abs_lt.mp habs
  unfold trialFactor trialComplement
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith only [hsq]

/-- The logarithmic barrier discrepancy of the trial factor from the exact factor. -/
noncomputable def discrepancy (w p v : V → ℝ) : ℝ :=
  ∑ i, w i * (trialFactor w v i / p i + p i / trialFactor w v i - 2)

omit [Fintype V] in
private lemma discrepancy_term_nonneg {w p v : V → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) (i : V) :
    0 ≤ w i * (trialFactor w v i / p i + p i / trialFactor w v i - 2) := by
  have ht := (trialFactor_spec (v := v) hw i).1
  have hEq : trialFactor w v i / p i + p i / trialFactor w v i - 2 =
      (trialFactor w v i - p i) ^ 2 / (p i * trialFactor w v i) := by
    field_simp [(hp i).ne', ht.ne']
    ring
  rw [hEq]
  exact mul_nonneg (hw i).le (div_nonneg (sq_nonneg _) (mul_nonneg (hp i).le ht.le))

lemma discrepancy_nonneg {w p v : V → ℝ} (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) :
    0 ≤ discrepancy w p v :=
  sum_nonneg fun i _ ↦ discrepancy_term_nonneg hw hp i

private lemma discrepancy_eq {w p q v : V → ℝ} (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i)
    (hpq : ∀ i, p i * q i = w i) :
    discrepancy w p v =
      (smooth w v ⬝ᵥ (p + q) - v ⬝ᵥ (p - q)) / 2 - 2 * mass w := by
  have hTerm (i : V) : w i * (trialFactor w v i / p i + p i / trialFactor w v i - 2) =
      (smooth w v i * (p i + q i) - v i * (p i - q i)) / 2 - 2 * w i := by
    obtain ⟨ht, _, htProd⟩ := trialFactor_spec (v := v) hw i
    have hQ : w i / p i = q i := (div_eq_iff (hp i).ne').mpr (by rw [mul_comm, hpq])
    have hT : w i / trialFactor w v i = trialComplement w v i :=
      (div_eq_iff ht.ne').mpr (by rw [mul_comm, htProd])
    calc
      _ = (w i / p i) * trialFactor w v i + (w i / trialFactor w v i) * p i - 2 * w i := by ring
      _ = _ := by rw [hQ, hT]; unfold trialFactor trialComplement; ring
  unfold discrepancy
  simp_rw [hTerm]
  simp only [dotProduct, Pi.add_apply, Pi.sub_apply, mass, sum_sub_distrib, mul_sum]
  rw [← Finset.sum_div, sum_sub_distrib]

omit [Fintype V] in
/-- The pointwise product equation gives the fixed-point equation for the exact difference. -/
lemma smooth_exact_difference {w p q : V → ℝ}
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hpq : ∀ i, p i * q i = w i) :
    smooth w (p - q) = p + q := by
  funext i
  change Real.sqrt ((p i - q i) ^ 2 + 4 * w i) = p i + q i
  rw [← hpq i, show (p i - q i) ^ 2 + 4 * (p i * q i) = (p i + q i) ^ 2 by ring,
    Real.sqrt_sq (add_nonneg (hp i).le (hq i).le)]

/-- The discrepancy is bounded by the Euclidean residual, as in the second part
of the manuscript's residual estimate. -/
theorem discrepancy_le_residual [Nonempty V] (K : (V → ℝ) →ₗ[ℝ] (V → ℝ))
    (hSelfAdj : ∀ x y, K x ⬝ᵥ y = x ⬝ᵥ K y)
    (hSquare : ∀ x, K (K x) = x - meanVector x)
    {w p q v : V → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) (hpq : ∀ i, p i * q i = w i)
    (hMassP : mass p = Real.sqrt (Fintype.card V * mass w))
    (hMassQ : mass q = Real.sqrt (Fintype.card V * mass w))
    (hFixed : K (p + q) = p - q) :
    discrepancy w p v ≤
      (norm₂ v + norm₂ (p - q) / 2) * norm₂ (v - K (smooth w v)) := by
  let N : ℝ := Fintype.card V
  let ω := mass w
  let u := smooth w v
  let f := p - q
  let r := v - K u
  let ζ := mass u / Real.sqrt N
  let s := Real.sqrt ω
  have hN : 0 < N := by dsimp [N]; positivity
  have hω : 0 ≤ ω := sum_nonneg fun i _ ↦ (hw i).le
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = ω := Real.sq_sqrt hω
  have hSqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hSqrtNSq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hMean : mass (p + q) / N = 2 * s / Real.sqrt N := by
    rw [mass_add, hMassP, hMassQ, Real.sqrt_mul (show 0 ≤ (Fintype.card V : ℝ) from hN.le)]
    change (Real.sqrt N * s + Real.sqrt N * s) / N = 2 * s / Real.sqrt N
    calc
      _ = (Real.sqrt N * s + Real.sqrt N * s) / Real.sqrt N ^ 2 := by
        rw [hSqrtNSq]
      _ = _ := by field_simp; ring
  have hProj : u ⬝ᵥ (p + q) = (K u ⬝ᵥ f) + mass u * (2 * s / Real.sqrt N) := by
    have hKf : K f = p + q - meanVector (p + q) := by
      change K (p - q) = _
      rw [← hFixed, hSquare]
    calc
      _ = (u ⬝ᵥ K f) + (u ⬝ᵥ meanVector (p + q)) := by
        rw [hKf, dotProduct_sub]
        ring
      _ = _ := by rw [← hSelfAdj, dotProduct_meanVector, mul_div_assoc, hMean]
  have hDelta : discrepancy w p v = s * (ζ - 2 * s) - (r ⬝ᵥ f) / 2 := by
    rw [discrepancy_eq hw hp hpq]
    change ((u ⬝ᵥ (p + q)) - v ⬝ᵥ f) / 2 - 2 * ω = _
    rw [hProj, show r ⬝ᵥ f = (v ⬝ᵥ f) - (K u ⬝ᵥ f) from sub_dotProduct _ _ _,
      ← hsSq]
    dsimp [ζ]
    ring
  have huSq : u ⬝ᵥ u = (v ⬝ᵥ v) + 4 * ω := by
    unfold dotProduct
    have hi (i : V) : u i * u i = v i * v i + 4 * w i := by
      have hn : 0 ≤ v i ^ 2 + 4 * w i :=
        add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (hw i).le)
      simpa only [u, smooth, pow_two] using (Real.sq_sqrt hn)
    simp_rw [hi, sum_add_distrib, ← mul_sum]
    rfl
  have hKuSq : K u ⬝ᵥ K u = (u ⬝ᵥ u) - ζ ^ 2 := by
    rw [hSelfAdj, hSquare, dotProduct_sub, dotProduct_meanVector]
    dsimp [ζ]
    rw [div_pow, hSqrtNSq, pow_two]
  have hRes : ζ ^ 2 - 4 * ω = 2 * (v ⬝ᵥ r) - (r ⬝ᵥ r) := by
    have hSym := dotProduct_comm (K u) v
    dsimp only [r]
    simp only [dotProduct_sub, sub_dotProduct]
    rw [hKuSq, huSq]
    linarith
  have hA : s * (ζ - 2 * s) ≤ norm₂ v * norm₂ r := by
    by_cases h : ζ ≤ 2 * s
    · exact (mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr h)).trans
        (mul_nonneg (norm₂_nonneg _) (norm₂_nonneg _))
    · have hBound : ζ ^ 2 - 4 * ω ≤ 2 * (norm₂ v * norm₂ r) := by
        have hC := (le_abs_self _).trans (abs_dotProduct_le v r)
        have hr : 0 ≤ r ⬝ᵥ r := by rw [← norm₂_sq]; positivity
        linarith
      calc
        _ ≤ ((ζ + 2 * s) / 2) * (ζ - 2 * s) :=
          mul_le_mul_of_nonneg_right (by linarith [lt_of_not_ge h]) (sub_nonneg.mpr (le_of_not_ge h))
        _ = (ζ ^ 2 - 4 * ω) / 2 := by rw [← hsSq]; ring
        _ ≤ _ := by linarith
  have hB : -(r ⬝ᵥ f) / 2 ≤ norm₂ f / 2 * norm₂ r := by
    have hC := (neg_le_abs _).trans (abs_dotProduct_le r f)
    rw [mul_comm (norm₂ r)] at hC
    linarith
  rw [hDelta, add_mul]
  linarith

private lemma abs_log_le_abs_sub_inv {a : ℝ} (ha : 0 < a) :
    |Real.log a| ≤ |a - a⁻¹| / 2 := by
  have h : |Real.log a| ≤ |Real.sinh (Real.log a)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log ha, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    at h

private lemma sq_log_le_ratio {a : ℝ} (ha : 0 < a) :
    Real.log a ^ 2 ≤ a + a⁻¹ - 2 := by
  let z := Real.log a / 2
  have hAbs : |z| ≤ |Real.sinh z| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hSq := sq_le_sq.mpr hAbs
  have hz : 2 * z = Real.log a := by dsimp [z]; ring
  have hCosh := Real.cosh_two_mul z
  rw [hz, Real.cosh_eq, Real.exp_neg, Real.exp_log ha] at hCosh
  have hIdentity := Real.cosh_sq_sub_sinh_sq z
  have hLogSq : Real.log a ^ 2 = 4 * z ^ 2 := by rw [← hz]; ring
  linarith

/-- The zero-coordinate estimate in the logarithmic residual bound. -/
theorem log_bound_of_discrepancy {w p v : V → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) (i₀ : V) (hWeight : w i₀ = 1) {t : ℝ}
    (ht : 0 < t) (hT : t ≤ Real.sqrt (mass w) * p i₀) :
    Real.log t ≤ Real.log (mass w) / 2 + |v i₀| / 2 + Real.sqrt (discrepancy w p v) := by
  classical
  let a := trialFactor w v i₀
  let b := trialComplement w v i₀
  have hSpec := trialFactor_spec (v := v) hw i₀
  have ha : 0 < a := hSpec.1
  have hAB : a * b = 1 := hSpec.2.2.trans hWeight
  have hInv : b = a⁻¹ := by
    rw [← one_div, eq_div_iff ha.ne', mul_comm]
    exact hAB
  have hDiff : a - b = v i₀ := by dsimp [a, b, trialFactor, trialComplement]; ring
  have hA : |Real.log a| ≤ |v i₀| / 2 := by
    rw [hInv] at hDiff
    simpa only [hDiff] using abs_log_le_abs_sub_inv ha
  have hTerm :
      Real.log (a / p i₀) ^ 2 ≤ w i₀ * (a / p i₀ + p i₀ / a - 2) := by
    simpa only [hWeight, one_mul, inv_div] using sq_log_le_ratio (div_pos ha (hp i₀))
  have hD : |Real.log (a / p i₀)| ≤ Real.sqrt (discrepancy w p v) :=
    Real.abs_le_sqrt (hTerm.trans (Finset.single_le_sum
      (fun j _ ↦ discrepancy_term_nonneg hw hp j) (mem_univ i₀)))
  have hω : 0 < mass w := sum_pos (fun j _ ↦ hw j) ⟨i₀, mem_univ _⟩
  have hLog := Real.log_le_log ht hT
  rw [Real.log_mul (Real.sqrt_pos.mpr hω).ne' (hp i₀).ne', Real.log_sqrt hω.le] at hLog
  rw [Real.log_div ha.ne' (hp i₀).ne'] at hD
  have ha' := (le_abs_self _).trans hA
  have hD' := (neg_le_abs _).trans hD
  linarith

end LovaszTheta.Circulant
