module

public import LovaszTheta.HermitePowerExpansion
public import LovaszTheta.PolynomialComparison

/-!
# Comparison for Hermite product tests

Expand each factor into powers. The sum of absolute power
coefficients is bounded by the product of factorials, hence by
the total degree factorial. The monomial comparison applies to
every tuple of powers, including repeated evaluation coordinates.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Classical Nat

namespace LovaszTheta.Circulant

variable {I J : Type*} [Fintype I] [Fintype J] {n : ℕ} [NeZero n]

/-- Evaluate a product of normalized Hermite factors, allowing repeated coordinates. -/
noncomputable def hermiteTest (r : J → I) (m : J → ℕ) (x : I → ℝ) : ℝ :=
  ∏ j, normalizedHermite (m j) (x (r j))

private abbrev PowerChoice (m : J → ℕ) := ∀ j, Fin (m j+1)

private noncomputable def powerChoiceCoeff {m : J → ℕ} (q : PowerChoice m) : ℝ :=
  ∏ j, hermitePowerCoeff (m j) (q j).val

omit [Fintype I] in
private lemma hermiteTest_eq_sum (r : J → I) (m : J → ℕ) (x : I → ℝ) :
    hermiteTest r m x = ∑ q : PowerChoice m, powerChoiceCoeff q * ∏ j, x (r j)^(q j).val := by
  unfold hermiteTest
  simp only [normalizedHermite_eq_sum_powers]
  rw [Fintype.prod_sum]
  exact sum_congr rfl fun q _ ↦ prod_mul_distrib

private lemma sum_abs_powerChoiceCoeff_le (m : J → ℕ) (M : ℕ) (hm : ∑ j, m j ≤ 2*M) :
    (∑ q : PowerChoice m, |powerChoiceCoeff q|) ≤ ((2*M)! : ℝ) := by
  simp only [powerChoiceCoeff,abs_prod]
  rw [← Fintype.prod_sum (fun (j : J) (z : Fin (m j+1)) ↦ |hermitePowerCoeff (m j) z.val|)]
  calc
    _ ≤ ∏ j, ((m j)! : ℝ) := prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
      (fun j _ ↦ sum_abs_hermitePowerCoeff_le (m j))
    _ ≤ _ := by
      rw [← Nat.cast_prod]
      exact_mod_cast (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum univ m)).trans
        (Nat.monotone_factorial hm)

omit [Fintype I] in
private lemma exists_powerChoice_positions (r : J → I) {m : J → ℕ} (q : PowerChoice m) :
    ∃ u : Fin (∑ j, (q j).val) → I, ∀ x : I → ℝ, (∏ p, x (u p)) = ∏ j, x (r j)^(q j).val := by
  let A := Σ j : J, Fin (q j).val
  have hA : Fintype.card A = ∑ j, (q j).val := by simp [A,Fintype.card_sigma]
  let e : Fin (∑ j, (q j).val) ≃ A := (Fintype.equivFinOfCardEq hA).symm
  refine ⟨fun p ↦ r (e p).1,fun x ↦ ?_⟩
  calc
    _ = ∏ a : A, x (r a.1) := e.prod_comp (fun a : A ↦ x (r a.1))
    _ = _ := by rw [Fintype.prod_sigma]; simp only [prod_const,card_univ,Fintype.card_fin]

/-- A Hermite product has the prescribed Gaussian expectation, up
to the comparison envelope, at any regular distinct family. -/
theorem abs_average_hermiteTest_sub_gaussian_le [Nonempty (InversionClass n)]
    (T : I → RootedTree) (k : I → ZMod n) (D M : ℕ)
    (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j)
    (r : J → I) (m : J → ℕ) (hm : ∑ j, m j ≤ 2*M) :
    |average (fun x ↦ hermiteTest r m (fun i ↦ (T i).field x (k i))) -
      ∫ x, hermiteTest r m x ∂gaussianCoordinates I| ≤
      ((2*M)! : ℝ) * (comparisonEnvelope 2 D M / Real.sqrt n) := by
  have hTerm (q : PowerChoice m) := exists_powerChoice_positions r q
  have hInt (q : PowerChoice m) : Integrable (fun x : I → ℝ ↦
      powerChoiceCoeff q * ∏ j, x (r j)^(q j).val) (gaussianCoordinates I) := by
    obtain ⟨u,hu⟩ := hTerm q
    simp_rw [← hu]
    exact (integrable_gaussianCoordinates_monomial u).const_mul _
  simp_rw [hermiteTest_eq_sum,average_sum,average_mul_left]
  rw [integral_finsetSum _ fun q _ ↦ hInt q,← sum_sub_distrib]
  simp_rw [integral_const_mul,← mul_sub]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ q : PowerChoice m, |powerChoiceCoeff q| * (comparisonEnvelope 2 D M / Real.sqrt n) := by
      apply sum_le_sum
      intro q _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      obtain ⟨u,hu⟩ := hTerm q
      have hField (x : InversionClass n → Bool) := (hu (fun i ↦ (T i).field x (k i))).symm
      simp_rw [hField, ← hu]
      have hDeg : (∑ j, (q j).val) ≤ 2*M :=
        (sum_le_sum fun j _ ↦ Nat.le_of_lt_succ (q j).isLt).trans hm
      exact abs_average_treeMonomial_sub_gaussian_le T k D M hD hk hDistinct hDeg u
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_abs_powerChoiceCoeff_le m M hm) (by unfold comparisonEnvelope; positivity)

omit [Fintype I] in
/-- The same growth estimate at all frequencies, without the covariance comparison. -/
theorem average_abs_hermiteTest_le (T : I → RootedTree) (k : I → ZMod n) (D M : ℕ)
    (hD : ∀ i, (T i).nodeCount ≤ D) (r : J → I) (m : J → ℕ) (hm : ∑ j, m j ≤ 2*M) :
    average (fun x ↦ |hermiteTest r m (fun i ↦ (T i).field x (k i))|) ≤
      ((2*M)! : ℝ) * comparisonEnvelope 2 D M := by
  simp_rw [hermiteTest_eq_sum]
  refine (average_mono (fun _ ↦ abs_sum_le_sum_abs _ _)).trans ?_
  simp_rw [abs_mul,average_sum,average_mul_left]
  calc
    _ ≤ ∑ q : PowerChoice m, |powerChoiceCoeff q| * comparisonEnvelope 2 D M := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      obtain ⟨u,hu⟩ := exists_powerChoice_positions r q
      have hField (x : InversionClass n → Bool) := (hu (fun i ↦ (T i).field x (k i))).symm
      simp_rw [hField]
      have hDeg : (∑ j, (q j).val) ≤ 2*M :=
        (sum_le_sum fun j _ ↦ Nat.le_of_lt_succ (q j).isLt).trans hm
      exact average_abs_treeMonomial_le T k D M hD hDeg u
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_abs_powerChoiceCoeff_le m M hm) (by unfold comparisonEnvelope; positivity)

end LovaszTheta.Circulant
