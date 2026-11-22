module

public import LovaszTheta.TreeLinearMoments

/-!
# Transfer of finite Gaussian linear combinations

The regular frequencies have near-identity covariance. At the
exceptional coordinates the uniform moment bound still applies,
and there are at most two such coordinates in the spatial average.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

/-- Replacing each centered Gaussian coordinate by its tree field. -/
noncomputable def treeLinearEvaluation (a : I → ℝ) (T : I → RootedTree)
    (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  ∑ i, a i*(T i).field x k

lemma treeLinearEvaluation_eq_linearWalsh (a : I → ℝ) (T : I → RootedTree)
    (x : InversionClass n → Bool) (k : ZMod n) :
    treeLinearEvaluation a T x k = linearWalsh a (treeCoefficients T (fun _ ↦ k)) x :=
  (linearWalsh_treeCoefficients a T (fun _ ↦ k) x).symm

private lemma average_indicator_eq_card {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) [DecidablePred p] :
    average (fun x ↦ if p x then (1 : ℝ) else 0) =
      (Fintype.card {x // p x} : ℝ) / Fintype.card Ω := by
  rw [average, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, Fintype.card_subtype]

/-- The exceptional frequencies have proportion at most two over the modulus. -/
lemma average_not_regularFrequency_le :
    average (fun k : ZMod n ↦ if ¬RegularFrequency k then (1 : ℝ) else 0) ≤ 2/(n : ℝ) := by
  rw [average_indicator_eq_card, ZMod.card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_not_regularFrequency_le (n := n)) (by positivity)

/-- The arbitrary-frequency mean square bound, including at frequency zero. -/
theorem average_treeLinearEvaluation_sq_le (a : I → ℝ) (T : I → RootedTree)
    (k : ZMod n) {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) :
    average (fun x ↦ treeLinearEvaluation a T x k ^ 2) ≤
      ((Fintype.card I : ℝ) * ∑ i, a i^2) * treeMomentEnvelope D := by
  simp_rw [treeLinearEvaluation_eq_linearWalsh]
  refine (average_linearWalsh_tree_sq_le a T (fun _ ↦ k) hD).trans ?_
  exact mul_le_mul_of_nonneg_right (sq_sum_abs_le_card_mul_sq a) (by unfold treeMomentEnvelope; positivity)

/-- Spatially averaged mean squares match the Gaussian variance, up
to the regular covariance error and the exceptional frequencies. -/
theorem abs_average_spatial_treeLinearEvaluation_sq_sub_le (a : I → ℝ) (T : I → RootedTree)
    {D : ℕ} (hD : ∀ i, (T i).nodeCount ≤ D) (hDistinct : ∀ i j,
      Nonempty ((T j).Isomorphism (T i)) → i = j) :
    |average (fun k : ZMod n ↦ average (fun x ↦ treeLinearEvaluation a T x k ^ 2)) -
      ∑ i, a i^2| ≤ ((Fintype.card I : ℝ) * ∑ i, a i^2) *
        (treeMomentEnvelope D / Real.sqrt n + (treeMomentEnvelope D+1)*(2/(n : ℝ))) := by
  let h (k : ZMod n) := average (fun x ↦ treeLinearEvaluation a T x k ^ 2)
  let v := ∑ i, a i^2
  let B := treeMomentEnvelope D
  let A := (Fintype.card I : ℝ)*v
  have hB : 0 ≤ B := by unfold B treeMomentEnvelope; positivity
  have hA : 0 ≤ A := by unfold A v; positivity
  have hv : v ≤ A := by
    by_cases he : IsEmpty I
    · let _ : IsEmpty I := he
      simp [A, v]
    · let _ : Nonempty I := not_isEmpty_iff.mp he
      have hp : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast (Fintype.card_pos (α := I))
      exact le_mul_of_one_le_left (by unfold v; positivity) hp
  have hR : 0 ≤ A*(B/Real.sqrt n) := by positivity
  have hPt (k : ZMod n) : |h k-v| ≤ A*(B/Real.sqrt n) + if ¬RegularFrequency k then A*(B+1) else 0 := by
    by_cases hk : RegularFrequency k
    · have hh : |h k-v| ≤ (∑ i, |a i|)^2*(B/Real.sqrt n) := by
        unfold h
        simp_rw [treeLinearEvaluation_eq_linearWalsh]
        exact abs_average_linearWalsh_tree_sq_sub_le a T (fun _ ↦ k) hD (fun _ ↦ hk)
          (fun i j hi _ ↦ hDistinct i j hi)
      simp only [hk, not_true_eq_false, ite_false, add_zero]
      exact hh.trans (mul_le_mul_of_nonneg_right (sq_sum_abs_le_card_mul_sq a) (by positivity))
    · have h₀ : 0 ≤ h k := average_sq_nonneg _
      have hv₀ : 0 ≤ v := by unfold v; positivity
      simp only [ite_eq_left hk]
      calc
        _ ≤ h k+v := (abs_sub _ _).trans_eq (by rw [abs_of_nonneg h₀, abs_of_nonneg hv₀])
        _ ≤ A*B+A := add_le_add (average_treeLinearEvaluation_sq_le a T k hD) hv
        _ = A*(B+1) := by ring
        _ ≤ _ := le_add_of_nonneg_left hR
  have hEq : average h-v = average (fun k ↦ h k-v) := by rw [average_sub, average_const]
  change |average h-v| ≤ _
  rw [hEq]
  refine (abs_average_le_average_abs _).trans ((average_mono hPt).trans ?_)
  rw [average_add, average_const]
  have hFactor (k : ZMod n) :
      (if ¬RegularFrequency k then A*(B+1) else 0) =
        (A*(B+1)) * (if ¬RegularFrequency k then 1 else 0) := by split_ifs <;> simp
  simp_rw [hFactor, average_mul_left]
  calc
    _ ≤ A*(B/Real.sqrt n) + (A*(B+1))*(2/(n : ℝ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left average_not_regularFrequency_le (by positivity)) _
    _ = _ := by ring

end LovaszTheta.Circulant
