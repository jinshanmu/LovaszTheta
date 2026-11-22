module

public import LovaszTheta.BranchingMomentExpansion

/-!
# Recursion for population moments

A term of highest child degree is a pure power of one child.
All other terms are bounded using the lower moments. At most as
many children as positions can contribute in those terms.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace LovaszTheta.Circulant.PlaneTree

private def constantToChild {j r : ℕ} (f : Fin r → Option (Fin j)) : Prop :=
  ∃ i : Fin j, ∀ t, f t = some i

private lemma sum_childMultiplicity_le {j r : ℕ} (f : Fin r → Option (Fin j)) :
    (∑ i, childMultiplicity f i) ≤ r := by
  have h := Finset.sum_fiberwise' (univ : Finset (Fin r)) f (fun _ ↦ (1 : ℕ))
  simp only [Fintype.sum_option, sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin] at h
  exact (Nat.le_add_left _ _).trans_eq h

private lemma card_nonzero_childMultiplicity_le {j r : ℕ} (f : Fin r → Option (Fin j)) :
    (univ.filter (fun i ↦ childMultiplicity f i ≠ 0)).card ≤ r := by
  let s := univ.filter (fun i ↦ childMultiplicity f i ≠ 0)
  calc
    s.card = ∑ i ∈ s, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ s, childMultiplicity f i :=
      sum_le_sum fun i hi ↦ Nat.pos_of_ne_zero (mem_filter.mp hi).2
    _ ≤ ∑ i, childMultiplicity f i := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := sum_childMultiplicity_le f

private lemma childMultiplicity_lt_of_not_constant {j r : ℕ} {f : Fin r → Option (Fin j)}
    (hf : ¬constantToChild f) (i : Fin j) : childMultiplicity f i < r := by
  let s := univ.filter (fun t ↦ f t = some i)
  by_contra hn
  have hcard : (univ : Finset (Fin r)).card ≤ s.card := by
    rw [card_univ, Fintype.card_fin]
    exact le_of_not_gt hn
  have he := eq_of_subset_of_card_le (subset_univ s) hcard
  exact hf ⟨i, fun t ↦ (mem_filter.mp (show t ∈ s from he ▸ mem_univ t)).2⟩

private lemma card_constantToChild_le (j r : ℕ) :
    (univ.filter (@constantToChild j r)).card ≤ j := by
  let c (i : Fin j) : Fin r → Option (Fin j) := fun _ ↦ some i
  have hs : univ.filter (@constantToChild j r) ⊆ univ.image c := by
    intro f hf
    obtain ⟨i, hi⟩ := (mem_filter.mp hf).2
    exact mem_image.mpr ⟨i, mem_univ _, funext fun t ↦ (hi t).symm⟩
  exact ((card_le_card hs).trans card_image_le).trans_eq (by simp)

private lemma product_childMoments_le_of_constant {p : ℕ → ℝ≥0∞} (hp : (∑' j, p j) = 1)
    {h j r : ℕ} {f : Fin r → Option (Fin j)} (hf : constantToChild f) :
    (∏ i, heightPopulationMoment p h (childMultiplicity f i)) ≤ heightPopulationMoment p h r := by
  obtain ⟨i, hi⟩ := hf
  calc
    _ ≤ ∏ k : Fin j, if k = i then heightPopulationMoment p h r else 1 := by
      apply prod_le_prod
      intro k _
      by_cases hk : k = i
      · subst k
        simp [childMultiplicity, hi]
      · have hzero : childMultiplicity f k = 0 := by
          simp [childMultiplicity, hi, Ne.symm hk]
        rw [ite_eq_right hk, hzero, heightPopulationMoment_zero_order]
        exact heightMass_le_one p hp h
    _ = _ := by simp

private lemma product_childMoments_le_of_not_constant {p : ℕ → ℝ≥0∞} (hp : (∑' j, p j) = 1)
    {h j r : ℕ} {L : ℝ≥0∞} (hL : 1 ≤ L) (hMom : ∀ s < r, heightPopulationMoment p h s ≤ L)
    {f : Fin r → Option (Fin j)} (hf : ¬constantToChild f) :
    (∏ i, heightPopulationMoment p h (childMultiplicity f i)) ≤ L^r := by
  calc
    _ ≤ ∏ i : Fin j, if childMultiplicity f i ≠ 0 then L else 1 := by
      apply prod_le_prod
      intro i _
      by_cases h₀ : childMultiplicity f i = 0
      · simp only [h₀, ne_eq, not_true_eq_false, ite_false, heightPopulationMoment_zero_order]
        exact heightMass_le_one p hp h
      · rw [ite_eq_left h₀]
        exact hMom _ (childMultiplicity_lt_of_not_constant hf i)
    _ = L^(univ.filter fun i ↦ childMultiplicity f i ≠ 0).card := by rw [← prod_filter, prod_const]
    _ ≤ _ := pow_le_pow_right₀ hL (card_nonzero_childMultiplicity_le f)

private lemma sum_products_childMoments_le {p : ℕ → ℝ≥0∞} (hp : (∑' j, p j) = 1)
    (h j r : ℕ) {L : ℝ≥0∞} (hL : 1 ≤ L) (hMom : ∀ s < r, heightPopulationMoment p h s ≤ L) :
    (∑ f : Fin r → Option (Fin j), ∏ i, heightPopulationMoment p h (childMultiplicity f i)) ≤
      (j : ℝ≥0∞)*heightPopulationMoment p h r + ((j+1 : ℕ) : ℝ≥0∞)^r*L^r := by
  let M := heightPopulationMoment p h r
  have hPure :
      (∑ f : Fin r → Option (Fin j), if constantToChild f then M else 0) ≤ (j : ℝ≥0∞)*M := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact_mod_cast card_constantToChild_le j r
  calc
    _ ≤ ∑ f : Fin r → Option (Fin j), ((if constantToChild f then M else 0) + L^r) := by
      apply sum_le_sum
      intro f _
      by_cases hf : constantToChild f
      · rw [ite_eq_left hf]
        exact (product_childMoments_le_of_constant hp hf).trans le_self_add
      · rw [ite_eq_right hf, zero_add]
        exact product_childMoments_le_of_not_constant hp hL hMom hf
    _ = (∑ f : Fin r → Option (Fin j), if constantToChild f then M else 0) +
        ((j+1 : ℕ) : ℝ≥0∞)^r*L^r := by
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun,
        Fintype.card_option, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    _ ≤ _ := add_le_add_left hPure _

/-- The highest moment has a linear term with coefficient the mean
offspring count. All other terms use only lower moments. -/
theorem heightPopulationMoment_step_le {p : ℕ → ℝ≥0∞} (hp : (∑' j, p j) = 1)
    (h r : ℕ) {L : ℝ≥0∞} (hL : 1 ≤ L) (hMom : ∀ s < r, heightPopulationMoment p h s ≤ L) :
    heightPopulationMoment p (h+1) r ≤
      (∑' j : ℕ, p j*(j : ℝ≥0∞))*heightPopulationMoment p h r +
        (∑' j : ℕ, p j*((j+1 : ℕ) : ℝ≥0∞)^r)*L^r := by
  rw [heightPopulationMoment_succ]
  refine (tsum_le_tsum fun j ↦
    mul_le_mul_of_nonneg_left (sum_products_childMoments_le hp h j r hL hMom) zero_le).trans_eq ?_
  simp_rw [mul_add, ← mul_assoc]
  rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
    ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

end LovaszTheta.Circulant.PlaneTree
