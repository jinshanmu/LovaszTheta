module

public import LovaszTheta.GraftSpatialEnergy
public import LovaszTheta.GraftTestMoments
public import LovaszTheta.LinearTransfer

/-!
# Quantitative grafting estimate

Single regular frequencies and regular distinct pairs give the
Gaussian squared moment and zero mixed moment. The exceptional
frequencies have small proportion and uniformly bounded moments.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma average_frequency_indicator (a : ZMod n) :
    average (fun b : ZMod n ↦ if b = a then (1 : ℝ) else 0) = 1/(n : ℝ) := by
  rw [average,Finset.sum_ite_eq',ite_eq_left (mem_univ a),ZMod.card]

private def badFrequencyPair (k j : ZMod n) : Prop :=
  ¬RegularFrequency k ∨ ¬RegularFrequency j ∨ j = k ∨ j = -k

private lemma average_badFrequencyPair_le :
    average (fun k : ZMod n ↦ average (fun j : ZMod n ↦ if badFrequencyPair k j then (1 : ℝ) else 0)) ≤ 6/(n : ℝ) := by
  let e (k : ZMod n) := if ¬RegularFrequency k then (1 : ℝ) else 0
  have h (k j : ZMod n) : (if badFrequencyPair k j then (1 : ℝ) else 0) ≤
      e k + e j + (if j = k then 1 else 0) + if j = -k then 1 else 0 := by
    have hNon (p : Prop) [Decidable p] : 0 ≤ (if p then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hk : 0 ≤ e k := hNon (¬RegularFrequency k)
    have hj : 0 ≤ e j := hNon (¬RegularFrequency j)
    have he := hNon (j = k)
    have hf := hNon (j = -k)
    by_cases h : badFrequencyPair k j
    · rw [ite_eq_left h]
      rcases h with h | h | h | h
      · have h₁ : e k = 1 := ite_eq_left h
        linarith only [h₁,hj,he,hf]
      · have h₁ : e j = 1 := ite_eq_left h
        linarith only [h₁,hk,he,hf]
      · rw [ite_eq_left h]
        linarith only [hk,hj,hf]
      · rw [ite_eq_left h]
        linarith only [hk,hj,he]
    · rw [ite_eq_right h]
      exact add_nonneg (add_nonneg (add_nonneg hk hj) he) hf
  calc
    _ ≤ average (fun k : ZMod n ↦ average (fun j : ZMod n ↦
        e k+e j+(if j=k then 1 else 0)+if j= -k then 1 else 0)) :=
      average_mono fun k ↦ average_mono (h k)
    _ = average e + average e + 1/(n : ℝ) + 1/(n : ℝ) := by
      simp_rw [average_add,average_frequency_indicator,average_const]
    _ ≤ _ := by
      have he : average e ≤ 2/(n : ℝ) := average_not_regularFrequency_le
      calc
        _ ≤ 2/(n : ℝ)+2/(n : ℝ)+1/(n : ℝ)+1/(n : ℝ) :=
          add_le_add_left (add_le_add_left (add_le_add he he) _) _
        _ = _ := by ring

namespace EvenTreeType

/-- The part of the grafting error due to the coefficient sum of the product tests. -/
noncomputable def graftProductErrorScale (D M : ℕ) : ℝ :=
  ((2*M)! : ℝ) * comparisonEnvelope 2 D M

theorem abs_average_spatial_hermiteField_sq_sub_one_le [Nonempty (InversionClass n)]
    (m : EvenTreeType →₀ ℕ) (D M : ℕ)
    (hD : ∀ i ∈ m.support, i.nodeCount ≤ D) (hM : m.toMultiset.card ≤ M) :
    |average (fun k : ZMod n ↦ average (fun x ↦ hermiteField m x k ^ 2))-1| ≤
      graftProductErrorScale D M / Real.sqrt n + (graftProductErrorScale D M + 1) * (2/(n : ℝ)) := by
  let Q := graftProductErrorScale D M
  let E (k : ZMod n) := average (fun x ↦ hermiteField m x k ^ 2)
  have hQ : 0 ≤ Q := by unfold Q graftProductErrorScale comparisonEnvelope; positivity
  have hPt (k : ZMod n) : |E k-1| ≤
      Q/Real.sqrt n + (Q+1) * (if ¬RegularFrequency k then 1 else 0) := by
    by_cases hk : RegularFrequency k
    · simp only [hk,not_true_eq_false,ite_false,mul_zero,add_zero]
      have h := abs_average_hermiteField_sq_sub_one_le m k hk D M hD hM
      dsimp only [Q]
      rw [graftProductErrorScale,mul_div_assoc]
      exact h
    · simp only [ite_eq_left hk,mul_one]
      have h := abs_average_hermiteField_product_le m k k D M hD hM
      simp only [← pow_two] at h
      calc
        _ ≤ |E k|+1 := (abs_sub _ _).trans_eq (by rw [abs_one])
        _ ≤ Q+1 := add_le_add_left h _
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have he : |average E-1| = |average (fun k ↦ E k-1)| := by rw [average_sub,average_const]
  change |average E-1| ≤ _
  rw [he]
  refine (abs_average_le_average_abs _).trans ((average_mono hPt).trans ?_)
  rw [average_add,average_const,average_mul_left]
  exact add_le_add_right (mul_le_mul_of_nonneg_left average_not_regularFrequency_le (by positivity)) _

theorem abs_average_spatial_hermiteField_product_le [Nonempty (InversionClass n)]
    (m : PositiveEvenHermiteIndex EvenTreeType) (D M : ℕ)
    (hD : ∀ i ∈ m.val.support, i.nodeCount ≤ D) (hM : m.val.toMultiset.card ≤ M) :
    |average (fun k : ZMod n ↦ average (fun j : ZMod n ↦
      average (fun x ↦ hermiteField m.val x k * hermiteField m.val x j)))| ≤
      graftProductErrorScale D M / Real.sqrt n + graftProductErrorScale D M*(6/(n : ℝ)) := by
  let Q := graftProductErrorScale D M
  let E (k j : ZMod n) := average (fun x ↦ hermiteField m.val x k*hermiteField m.val x j)
  have hQ : 0 ≤ Q := by unfold Q graftProductErrorScale comparisonEnvelope; positivity
  have hPt (k j : ZMod n) :
      |E k j| ≤ Q/Real.sqrt n + Q*(if badFrequencyPair k j then 1 else 0) := by
    by_cases h : badFrequencyPair k j
    · rw [ite_eq_left h,mul_one]
      exact (abs_average_hermiteField_product_le m.val k j D M hD hM).trans
        (le_add_of_nonneg_left (by positivity))
    · have hk : RegularFrequency k := Classical.byContradiction (fun hn ↦ h (Or.inl hn))
      have hj : RegularFrequency j := Classical.byContradiction (fun hn ↦ h (Or.inr (Or.inl hn)))
      have hkj : j ≠ k ∧ j ≠ -k := ⟨fun he ↦ h (Or.inr (Or.inr (Or.inl he))),
        fun he ↦ h (Or.inr (Or.inr (Or.inr he)))⟩
      rw [ite_eq_right h,mul_zero,add_zero]
      dsimp only [Q]
      rw [graftProductErrorScale,mul_div_assoc]
      exact abs_average_hermiteField_product_le_regular m k j hk hj hkj D M hD hM
  change |average (fun k ↦ average (E k))| ≤ _
  refine (abs_average_le_average_abs _).trans
    ((average_mono (fun k ↦ abs_average_le_average_abs (E k))).trans ?_)
  refine (average_mono (fun k ↦ average_mono (hPt k))).trans ?_
  simp_rw [average_add,average_const,average_mul_left]
  exact add_le_add_right (mul_le_mul_of_nonneg_left average_badFrequencyPair_le hQ) _

lemma graft_nodeCount_le (m : PositiveEvenHermiteIndex EvenTreeType) (D M : ℕ)
    (hD : ∀ i ∈ m.val.support, i.nodeCount ≤ D) (hM : m.val.toMultiset.card ≤ M) :
    (graftOfIndex m).representative.nodeCount ≤ 1+D*M := by
  rw [representative_nodeCount,nodeCount_graftOfIndex]
  apply Nat.add_le_add_left
  have he : (∑ i : m.val.support, m.val i.val) = m.val.toMultiset.card := by
    rw [Finsupp.card_toMultiset,Finsupp.sum]
    exact sum_coe_sort _ m.val
  calc
    _ ≤ ∑ i : m.val.support, m.val i.val*D := sum_le_sum fun i _ ↦
      Nat.mul_le_mul_left _ ((representative_nodeCount i.val).trans_le (hD i.val i.property))
    _ ≤ _ := by rw [← sum_mul,he,mul_comm]; exact Nat.mul_le_mul_left D hM

/-- The scalar error in the spatial mean-square estimate for one Hermite product. -/
noncomputable def graftResidualError (D M n : ℕ) : ℝ :=
  graftProductErrorScale D M * (2/Real.sqrt n+8/(n : ℝ)) +
    treeMomentEnvelope (1+D*M)/Real.sqrt n + (treeMomentEnvelope (1+D*M)+2)*(2/(n : ℝ))

/-- The spatial mean square of the difference between the
multiplied Hermite product and its grafted field. -/
theorem average_spatial_sq_graftResidual_le [Nonempty (InversionClass n)]
    (m : PositiveEvenHermiteIndex EvenTreeType) (D M : ℕ)
    (hD : ∀ i ∈ m.val.support, i.nodeCount ≤ D) (hM : m.val.toMultiset.card ≤ M) :
    average (fun k : ZMod n ↦ average (fun x ↦
      (signOperator x (hermiteField m.val x) k - (graftOfIndex m).representative.field x k)^2)) ≤
      graftResidualError D M n := by
  have hSingle := abs_average_spatial_hermiteField_sq_sub_one_le m.val D M hD hM (n := n)
  have hPair := abs_average_spatial_hermiteField_product_le m D M hD hM (n := n)
  have hGraft := abs_average_spatial_treeLinearEvaluation_sq_sub_le
    (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ (graftOfIndex m).representative)
    (fun _ ↦ graft_nodeCount_le m D M hD hM) (fun _ _ _ ↦ Subsingleton.elim _ _) (n := n)
  simp only [treeLinearEvaluation,Fintype.sum_unique,one_mul,one_pow,Fintype.card_unit,Nat.cast_one] at hGraft
  rw [average_spatial_sq_graftResidual]
  unfold graftResidualError
  linear_combination (norm := ring_nf)
    (abs_le.mp hSingle).2 + (abs_le.mp hPair).1 + (abs_le.mp hGraft).1
  exact le_rfl

end EvenTreeType

end LovaszTheta.Circulant
