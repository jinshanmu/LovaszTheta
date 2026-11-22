module

public import LovaszTheta.UnorderedBranching

/-!
# Recursive Gaussian coefficients

The Hermite coefficient at the root is multiplied by the child
coefficients and the square root of their multinomial ordering
count. Squaring the recursion gives the unordered branching law.
-/

@[expose] public section

open Finset
open scoped Classical ENNReal

namespace LovaszTheta.Circulant.EvenTreeType

/-- The type with no children. -/
noncomputable def leaf : EvenTreeType := graft 0 (by simp)

@[simp]
lemma children_leaf : (children leaf).val = 0 :=
  congrArg Subtype.val (children_graft _ _)

@[simp]
lemma childList_leaf : childList leaf = [] := by simp [childList]

/-- The root amplitude before the children are grafted. -/
noncomputable def offspringAmplitude (τ σ : ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 2 else activationCoefficient τ σ j)/σ

lemma offspringAmplitude_sq (τ σ : ℝ) (j : ℕ) :
    offspringAmplitude τ σ j ^ 2 = gaussianOffspringProbability τ σ j := by
  unfold offspringAmplitude gaussianOffspringProbability
  rw [div_pow]
  split_ifs <;> norm_num

/-- The signed coefficient of a tree in the unit-variance Gaussian. -/
noncomputable def gaussianCoefficient (τ σ : ℝ) (T : EvenTreeType) : ℝ :=
  let f (i : Fin T.childList.length) := T.childList[i]
  offspringAmplitude τ σ T.childList.length * Real.sqrt (Fintype.card (FamilyOrdering f)) *
    ∏ i : Fin T.childList.length, gaussianCoefficient τ σ T.childList[i]
termination_by T.nodeCount
decreasing_by exact childList_nodeCount_lt T i

private lemma card_familyOrdering_eq_one_of_empty {I A : Type*} [Fintype I] [IsEmpty I] (f : I → A) :
    Fintype.card (FamilyOrdering f) = 1 := by
  let _ : Unique (FamilyOrdering f) :=
    { default := ⟨f,rfl⟩
      uniq := fun _ ↦ Subtype.ext (funext fun i ↦ isEmptyElim i) }
  exact Fintype.card_unique

@[simp]
theorem gaussianCoefficient_leaf (τ σ : ℝ) : gaussianCoefficient τ σ leaf = 2/σ := by
  rw [gaussianCoefficient]
  have h : IsEmpty (Fin leaf.childList.length) := by rw [childList_leaf]; exact inferInstanceAs (IsEmpty (Fin 0))
  let _ := h
  simp [offspringAmplitude, card_familyOrdering_eq_one_of_empty]

/-- The squared coefficient is exactly the probability of that
unordered tree under the Gaussian offspring law. -/
theorem ofReal_gaussianCoefficient_sq (τ σ : ℝ) (T : EvenTreeType) :
    ENNReal.ofReal (gaussianCoefficient τ σ T ^ 2) =
      branchingProbability (fun j ↦ ENNReal.ofReal (gaussianOffspringProbability τ σ j)) T := by
  induction h : T.nodeCount using Nat.strong_induction_on generalizing T with
  | ind d ih =>
    let f (i : Fin T.childList.length) := T.childList[i]
    let p (j : ℕ) := ENNReal.ofReal (gaussianOffspringProbability τ σ j)
    have hP := branchingProbability_graftOfFn (childList_even T) f p
    rw [graftOfFn_childList T] at hP
    have hLower (i : Fin T.childList.length) :
        ENNReal.ofReal (gaussianCoefficient τ σ (f i)^2) = branchingProbability p (f i) :=
      ih _ ((childList_nodeCount_lt T i).trans_eq h) _ rfl
    rw [hP, gaussianCoefficient]
    change ENNReal.ofReal ((offspringAmplitude τ σ T.childList.length *
      Real.sqrt (Fintype.card (FamilyOrdering f)) * (∏ i, gaussianCoefficient τ σ (f i)))^2) = _
    have hN := gaussianOffspringProbability_nonneg τ σ T.childList.length
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), offspringAmplitude_sq,
      ← Finset.prod_pow, ENNReal.ofReal_mul (mul_nonneg hN (by positivity)), ENNReal.ofReal_mul hN,
      ENNReal.ofReal_natCast, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ by positivity)]
    simp only [hLower]
    unfold p
    ac_rfl

/-- The squared coefficients sum to one. -/
theorem hasSum_gaussianCoefficient_sq {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    HasSum (fun T ↦ gaussianCoefficient τ σ T ^ 2) 1 := by
  have hP := (gaussian_branchingProbability_mass_and_moments hτ hσ hσ' hMean).1
  simp_rw [← ofReal_gaussianCoefficient_sq] at hP
  have hS := ENNReal.hasSum_toReal (hP ▸ ENNReal.one_ne_top)
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hS
  have hM := congrArg ENNReal.toReal hP
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top), ENNReal.toReal_one] at hM
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hM
  rwa [hM] at hS

/-- Every size moment of the squared coefficients is finite. -/
theorem summable_gaussianCoefficient_sq_mul_size_pow {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) (p : ℕ) :
    Summable (fun T : EvenTreeType ↦ gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) := by
  have hP := (gaussian_branchingProbability_mass_and_moments hτ hσ hσ' hMean).2 p
  simp_rw [← ofReal_gaussianCoefficient_sq] at hP
  have h := ENNReal.summable_toReal hP
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (sq_nonneg _)] using h

/-- The squared coefficient tail is controlled by every size moment. -/
theorem gaussianCoefficient_sq_tail_le {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))
    {D : ℕ} (hD : 0 < D) (p : ℕ) :
    (∑' T : EvenTreeType, if D < T.nodeCount then gaussianCoefficient τ σ T ^ 2 else 0) ≤
      (∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) / (D : ℝ)^p := by
  have hS := (hasSum_gaussianCoefficient_sq hτ hσ hσ' hMean).summable
  have hTail : Summable (fun T : EvenTreeType ↦ if D < T.nodeCount then gaussianCoefficient τ σ T ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun T ↦ by split_ifs <;> positivity)
      (fun T ↦ by split_ifs <;> simp only [le_refl, sq_nonneg]) hS
  have hMoment := summable_gaussianCoefficient_sq_mul_size_pow hτ hσ hσ' hMean p
  rw [← tsum_div_const]
  apply hTail.tsum_le_tsum _ (hMoment.div_const _)
  intro T
  change (if D < T.nodeCount then gaussianCoefficient τ σ T ^ 2 else 0) ≤
    gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p / (D : ℝ)^p
  by_cases ht : D < T.nodeCount
  · rw [ite_eq_left ht,le_div_iff₀ (by positivity : 0 < (D : ℝ)^p)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast ht.le) _) (sq_nonneg _)
  · rw [ite_eq_right ht]
    positivity

end LovaszTheta.Circulant.EvenTreeType
