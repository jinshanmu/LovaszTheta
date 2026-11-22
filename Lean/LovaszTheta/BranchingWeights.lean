module

public import Mathlib.Data.W.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Finite ordered trees and branching weights

The weight is the probability of the specified offspring counts.
Restricting the height makes the root weight factor into the heights
of the child trees, so the total mass satisfies the offspring recursion.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace LovaszTheta.Circulant

/-- A finite ordered rooted tree. -/
abbrev PlaneTree := WType (fun j : ℕ ↦ Fin j)

namespace PlaneTree

/-- The total population of the tree. -/
def population : PlaneTree → ℕ :=
  WType.elim ℕ (fun b ↦ 1+∑ i, b.2 i)

@[simp]
lemma population_mk (j : ℕ) (c : Fin j → PlaneTree) :
    population (WType.mk j c) = 1+∑ i, population (c i) := rfl

lemma population_pos (t : PlaneTree) : 0 < population t := by
  cases t
  simp only [population_mk]
  omega

/-- The product of offspring probabilities at the nodes. -/
noncomputable def weight (p : ℕ → ℝ≥0∞) : PlaneTree → ℝ≥0∞ :=
  WType.elim ℝ≥0∞ (fun b ↦ p b.1 * ∏ i, b.2 i)

@[simp]
lemma weight_mk (p : ℕ → ℝ≥0∞) (j : ℕ) (c : Fin j → PlaneTree) :
    weight p (WType.mk j c) = p j * ∏ i, weight p (c i) := rfl

/-- The weight of the tree restricted to a height cutoff. -/
noncomputable def weightThroughHeight (p : ℕ → ℝ≥0∞) (h : ℕ) (t : PlaneTree) : ℝ≥0∞ :=
  if t.depth ≤ h then weight p t else 0

@[simp]
lemma weightThroughHeight_zero (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    weightThroughHeight p 0 t = 0 := by
  simp only [weightThroughHeight, ite_eq_right (not_le_of_gt (WType.depth_pos t))]

private lemma depth_mk_le_succ_iff (j : ℕ) (c : Fin j → PlaneTree) (h : ℕ) :
    (WType.mk j c).depth ≤ h+1 ↔ ∀ i, (c i).depth ≤ h := by
  change (univ.sup fun i ↦ (c i).depth)+1 ≤ h+1 ↔ _
  rw [Nat.succ_le_succ_iff, Finset.sup_le_iff]
  simp only [mem_univ, true_implies]

/-- At positive height, truncating the tree amounts to truncating
each of its children at the previous height. -/
lemma weightThroughHeight_succ_mk (p : ℕ → ℝ≥0∞) (h j : ℕ) (c : Fin j → PlaneTree) :
    weightThroughHeight p (h+1) (WType.mk j c) =
      p j * ∏ i, weightThroughHeight p h (c i) := by
  by_cases hc : ∀ i, (c i).depth ≤ h
  · have he := (depth_mk_le_succ_iff j c h).mpr hc
    simp [weightThroughHeight, he, hc]
  · have he : ¬(WType.mk j c).depth ≤ h+1 := fun hh ↦ hc ((depth_mk_le_succ_iff j c h).mp hh)
    unfold weightThroughHeight
    rw [ite_eq_right he]
    push Not at hc
    obtain ⟨i, hi⟩ := hc
    rw [Finset.prod_eq_zero (mem_univ i) (ite_eq_right (not_le_of_gt hi)), mul_zero]

lemma weightThroughHeight_mono (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    Monotone (fun h ↦ weightThroughHeight p h t) := by
  intro h k hhk
  unfold weightThroughHeight
  by_cases h₁ : t.depth ≤ h
  · simp [h₁, h₁.trans hhk]
  · simp [h₁]

lemma iSup_weightThroughHeight (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    (⨆ h, weightThroughHeight p h t) = weight p t := by
  apply le_antisymm
  · exact iSup_le fun h ↦ by unfold weightThroughHeight; split_ifs <;> simp
  · exact (le_iSup (fun h ↦ weightThroughHeight p h t) t.depth).trans' (by
      unfold weightThroughHeight
      rw [ite_eq_left le_rfl])

/-- Factoring the sum over independent child choices. -/
theorem tsum_product_fin {j : ℕ} {A : Fin j → Type*} (f : ∀ i, A i → ℝ≥0∞) :
    (∑' a : ∀ i, A i, ∏ i, f i (a i)) = ∏ i, ∑' b : A i, f i b := by
  induction j with
  | zero => simp
  | succ j ih =>
    let e : (∀ i, A i) ≃ A 0 × (∀ i : Fin j, A i.succ) := (Fin.consEquiv A).symm
    calc
      _ = ∑' ab : A 0 × (∀ i : Fin j, A i.succ), ∏ i, f i (e.symm ab i) := (e.symm.tsum_eq _).symm
      _ = ∑' (a : A 0) (b : ∀ i : Fin j, A i.succ), f 0 a * ∏ i, f i.succ (b i) := by
        rw [tsum_prod']
        apply tsum_congr
        intro a
        apply tsum_congr
        intro b
        have h₀ : e.symm (a,b) 0 = a := Fin.cons_zero a b
        have h₁ (i : Fin j) : e.symm (a,b) i.succ = b i := Fin.cons_succ a b i
        simp only [Fin.prod_univ_succ, h₀, h₁]
      _ = _ := by
        simp_rw [ENNReal.tsum_mul_left, ih]
        rw [ENNReal.tsum_mul_right, Fin.prod_univ_succ]

/-- The total mass of the trees up to the height cutoff. -/
noncomputable def heightMass (p : ℕ → ℝ≥0∞) (h : ℕ) : ℝ≥0∞ :=
  ∑' t : PlaneTree, weightThroughHeight p h t

@[simp]
lemma heightMass_zero (p : ℕ → ℝ≥0∞) : heightMass p 0 = 0 := by simp [heightMass]

/-- The height mass is evaluated by the offspring probability
generating function at the previous height mass. -/
theorem heightMass_succ (p : ℕ → ℝ≥0∞) (h : ℕ) :
    heightMass p (h+1) = ∑' j, p j * (heightMass p h)^j := by
  let e : PlaneTree ≃ Σ j : ℕ, Fin j → PlaneTree := WType.equivSigma _
  unfold heightMass
  rw [← e.symm.tsum_eq, tsum_sigma']
  apply tsum_congr
  intro j
  simp_rw [show ∀ c : Fin j → PlaneTree, e.symm ⟨j, c⟩ = WType.mk j c from fun _ ↦ rfl,
    weightThroughHeight_succ_mk, ENNReal.tsum_mul_left,
    tsum_product_fin (fun _ : Fin j ↦ weightThroughHeight p h), prod_const, card_univ, Fintype.card_fin]

lemma heightMass_le_one (p : ℕ → ℝ≥0∞) (hp : (∑' j, p j) = 1) (h : ℕ) :
    heightMass p h ≤ 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [heightMass_succ, ← hp]
    exact tsum_le_tsum fun j ↦ by
      calc
        _ ≤ p j * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le ih) zero_le
        _ = _ := mul_one _

/-- Truncated masses increase to the sum over all finite trees. -/
theorem iSup_heightMass (p : ℕ → ℝ≥0∞) :
    (⨆ h, heightMass p h) = ∑' t : PlaneTree, weight p t := by
  apply le_antisymm
  · refine iSup_le fun h ↦ tsum_le_tsum fun t ↦ ?_
    unfold weightThroughHeight
    split_ifs <;> simp
  · rw [tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    let h := s.sup WType.depth
    calc
      _ = ∑ t ∈ s, weightThroughHeight p h t := sum_congr rfl fun t ht ↦ by
        unfold weightThroughHeight h
        rw [ite_eq_left (Finset.le_sup ht)]
      _ ≤ heightMass p h := by
        unfold heightMass
        rw [tsum_eq_iSup_sum]
        exact le_iSup (fun s : Finset PlaneTree ↦ ∑ t ∈ s, weightThroughHeight p h t) s
      _ ≤ _ := le_iSup (heightMass p) h

end PlaneTree

end LovaszTheta.Circulant
