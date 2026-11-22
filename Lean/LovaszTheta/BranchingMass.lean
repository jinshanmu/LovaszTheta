module

public import LovaszTheta.BranchingWeights
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

/-!
# Normalization of the subcritical tree weights

The missing mass below a given height contracts by the mean number
of offspring. Hence the branching weights sum to one over finite trees.
-/

@[expose] public section

open Finset Filter
open scoped ENNReal Topology

namespace LovaszTheta.Circulant.PlaneTree

private lemma heightMass_toReal_succ (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hMass : HasSum a 1) (h : ℕ) :
    let p : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (a j)
    (heightMass p (h+1)).toReal = ∑' j, a j*((heightMass p h).toReal)^j := by
  let p : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (a j)
  have hP : ∑' j, p j = 1 := by
    unfold p
    rw [← ENNReal.ofReal_tsum_of_nonneg ha hMass.summable, hMass.tsum_eq, ENNReal.ofReal_one]
  have hTop : heightMass p h ≠ ∞ := ne_of_lt ((heightMass_le_one p hP h).trans_lt ENNReal.one_lt_top)
  change (heightMass p (h+1)).toReal = _
  rw [heightMass_succ, ENNReal.tsum_toReal_eq
    (fun j ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hTop))]
  apply tsum_congr
  intro j
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, p, ENNReal.toReal_ofReal (ha j)]

private lemma one_sub_pow_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (j : ℕ) :
    1-s^j ≤ (j : ℝ)*(1-s) := by
  have h := abs_pow_sub_pow_le (a := (1 : ℝ)) (b := s) (n := j)
  rwa [one_pow, abs_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hs hs')),
    abs_of_nonneg (sub_nonneg.mpr hs'), abs_one, abs_of_nonneg hs, max_eq_left hs',
    one_pow, mul_one, mul_comm (1-s)] at h

/-- The weights of the finite trees have mass one when the
offspring law has mean less than one. -/
theorem tsum_weight_eq_one_of_subcritical (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hMass : HasSum a 1)
    {m : ℝ} (hm : HasSum (fun j : ℕ ↦ (j : ℝ)*a j) m) (hm' : m < 1) :
    (∑' t : PlaneTree, weight (fun j ↦ ENNReal.ofReal (a j)) t) = 1 := by
  let p : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (a j)
  let M (h : ℕ) := (heightMass p h).toReal
  have hP : ∑' j, p j = 1 := by
    unfold p
    rw [← ENNReal.ofReal_tsum_of_nonneg ha hMass.summable, hMass.tsum_eq, ENNReal.ofReal_one]
  have hM₀ (h : ℕ) : 0 ≤ M h := ENNReal.toReal_nonneg
  have hM₁ (h : ℕ) : M h ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (heightMass_le_one p hP h)
  have hRec (h : ℕ) : M (h+1) = ∑' j, a j*M h^j := heightMass_toReal_succ a ha hMass h
  have hm₀ : 0 ≤ m := by
    rw [← hm.tsum_eq]
    exact tsum_nonneg fun j ↦ mul_nonneg (by positivity) (ha j)
  have hContract (h : ℕ) : 1-M (h+1) ≤ m*(1-M h) := by
    let s := M h
    have hs := hM₀ h
    have hs' := hM₁ h
    have hS : Summable (fun j ↦ a j*s^j) := Summable.of_nonneg_of_le
      (fun j ↦ mul_nonneg (ha j) (pow_nonneg hs _))
      (fun j ↦ mul_le_of_le_one_right (ha j) (pow_le_one₀ hs hs'))
      hMass.summable
    have hPt (j : ℕ) : a j-a j*s^j ≤ ((j : ℝ)*a j)*(1-s) := by
      have h := mul_le_mul_of_nonneg_left (one_sub_pow_le hs hs' j) (ha j)
      nlinarith only [h]
    calc
      _ = ∑' j, (a j-a j*s^j) := by rw [hMass.summable.tsum_sub hS, hMass.tsum_eq, hRec]
      _ ≤ ∑' j : ℕ, ((j : ℝ)*a j)*(1-s) :=
        Summable.tsum_le_tsum hPt (hMass.summable.sub hS) (hm.summable.mul_right _)
      _ = _ := by rw [tsum_mul_right, hm.tsum_eq]
  have hMissing (h : ℕ) : 1-M h ≤ m^h := by
    induction h with
    | zero => simp [M]
    | succ h ih =>
      rw [pow_succ']
      exact (hContract h).trans (mul_le_mul_of_nonneg_left ih hm₀)
  have hLim : Tendsto M atTop (𝓝 1) := by
    have hPow : Tendsto (fun h : ℕ ↦ m^h) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hm₀])
    have hLow : Tendsto (fun h : ℕ ↦ 1-m^h) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hPow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLow tendsto_const_nhds
      (fun h ↦ by linarith only [hMissing h]) hM₁
  let q := ∑' t, weight p t
  have hq : q ≤ 1 := by
    unfold q
    rw [← iSup_heightMass p]
    exact iSup_le (heightMass_le_one p hP)
  have hQ : 1 ≤ q.toReal := le_of_tendsto hLim (Eventually.of_forall fun h ↦
    ENNReal.toReal_mono (ne_of_lt (hq.trans_lt ENNReal.one_lt_top)) (by
      unfold q
      rw [← iSup_heightMass]
      exact le_iSup (heightMass p) h))
  have hqR : q.toReal ≤ 1 :=
    (ENNReal.toReal_mono ENNReal.one_ne_top hq).trans_eq ENNReal.toReal_one
  have hOfReal := congrArg ENNReal.ofReal (le_antisymm hqR hQ)
  rwa [ENNReal.ofReal_toReal (ne_of_lt (hq.trans_lt ENNReal.one_lt_top)), ENNReal.ofReal_one] at hOfReal

end LovaszTheta.Circulant.PlaneTree
