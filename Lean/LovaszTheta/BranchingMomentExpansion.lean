module

public import LovaszTheta.BranchingWeights
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option

/-!
# Expanding the moments of the tree population

A choice function records which child contributes each factor in
the power of the population. Grouping its fibers gives the product
of the corresponding lower-height moments.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace LovaszTheta.Circulant.PlaneTree

/-- The truncated population moment of a branching tree. -/
noncomputable def heightPopulationMoment (p : ℕ → ℝ≥0∞) (h r : ℕ) : ℝ≥0∞ :=
  ∑' t : PlaneTree, weightThroughHeight p h t * (population t : ℝ≥0∞)^r

@[simp]
lemma heightPopulationMoment_zero_height (p : ℕ → ℝ≥0∞) (r : ℕ) :
    heightPopulationMoment p 0 r = 0 := by simp [heightPopulationMoment]

@[simp]
lemma heightPopulationMoment_zero_order (p : ℕ → ℝ≥0∞) (h : ℕ) :
    heightPopulationMoment p h 0 = heightMass p h := by
  simp [heightPopulationMoment, heightMass]

/-- How often a position in the population power is assigned to the given child. -/
def childMultiplicity {j r : ℕ} (f : Fin r → Option (Fin j)) (i : Fin j) : ℕ :=
  (univ.filter fun t ↦ f t = some i).card

private lemma population_power_expand {j : ℕ} (v : Fin j → ℝ≥0∞) (r : ℕ) :
    (1+∑ i, v i)^r = ∑ f : Fin r → Option (Fin j), ∏ i, (v i)^(childMultiplicity f i) := by
  let w : Option (Fin j) → ℝ≥0∞ := Option.elim' 1 v
  have hSum : (∑ u, w u) = 1+∑ i, v i := by simp only [Fintype.sum_option, w, Option.elim'_none, Option.elim'_some]
  have hPow := Fintype.prod_sum (fun (_ : Fin r) (u : Option (Fin j)) ↦ w u)
  simp only [prod_const, card_univ, Fintype.card_fin, hSum] at hPow
  rw [hPow]
  apply sum_congr rfl
  intro f _
  rw [← Finset.prod_fiberwise' (univ : Finset (Fin r)) f w, Fintype.prod_option]
  have h₀ : (∏ t ∈ (univ : Finset (Fin r)) with f t = none, w none) = 1 := by
    simp only [w, Option.elim'_none, prod_const_one]
  rw [h₀, one_mul]
  apply prod_congr rfl
  intro i _
  simp only [prod_const, childMultiplicity, w, Option.elim'_some]

private lemma tsum_children_population_power (p : ℕ → ℝ≥0∞) (h j r : ℕ) :
    (∑' c : Fin j → PlaneTree,
      (∏ i, weightThroughHeight p h (c i)) * (1+∑ i, (population (c i) : ℝ≥0∞))^r) =
      ∑ f : Fin r → Option (Fin j), ∏ i, heightPopulationMoment p h (childMultiplicity f i) := by
  simp_rw [population_power_expand (r := r), mul_sum, ← prod_mul_distrib]
  rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
  apply sum_congr rfl
  intro f _
  exact tsum_product_fin
    (fun i t ↦ weightThroughHeight p h t * (population t : ℝ≥0∞)^(childMultiplicity f i))

/-- The next-height moment is the offspring average of the power
expansion in the child moments. -/
theorem heightPopulationMoment_succ (p : ℕ → ℝ≥0∞) (h r : ℕ) :
    heightPopulationMoment p (h+1) r =
      ∑' j : ℕ, p j*(∑ f : Fin r → Option (Fin j), ∏ i, heightPopulationMoment p h (childMultiplicity f i)) := by
  let e : PlaneTree ≃ Σ j : ℕ, Fin j → PlaneTree := WType.equivSigma _
  unfold heightPopulationMoment at *
  rw [← e.symm.tsum_eq, tsum_sigma']
  apply tsum_congr
  intro j
  simp_rw [show ∀ c : Fin j → PlaneTree, e.symm ⟨j, c⟩ = WType.mk j c from fun _ ↦ rfl,
    weightThroughHeight_succ_mk, population_mk, mul_assoc, ENNReal.tsum_mul_left]
  push_cast
  congr 1
  exact tsum_children_population_power p h j r

/-- Increasing the cutoff recovers the moment over finite trees. -/
theorem iSup_heightPopulationMoment (p : ℕ → ℝ≥0∞) (r : ℕ) :
    (⨆ h, heightPopulationMoment p h r) =
      ∑' t : PlaneTree, weight p t * (population t : ℝ≥0∞)^r := by
  apply le_antisymm
  · refine iSup_le fun h ↦ tsum_le_tsum fun t ↦ ?_
    unfold weightThroughHeight
    split_ifs <;> simp
  · rw [tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    let h := s.sup WType.depth
    calc
      _ = ∑ t ∈ s, weightThroughHeight p h t * (population t : ℝ≥0∞)^r := sum_congr rfl fun t ht ↦ by
        unfold weightThroughHeight h
        rw [ite_eq_left (Finset.le_sup ht)]
      _ ≤ heightPopulationMoment p h r := by
        unfold heightPopulationMoment
        rw [tsum_eq_iSup_sum]
        exact le_iSup (fun s : Finset PlaneTree ↦
          ∑ t ∈ s, weightThroughHeight p h t * (population t : ℝ≥0∞)^r) s
      _ ≤ _ := le_iSup (fun h ↦ heightPopulationMoment p h r) h

end LovaszTheta.Circulant.PlaneTree
