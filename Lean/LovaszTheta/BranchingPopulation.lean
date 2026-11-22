module

public import LovaszTheta.BranchingMass
public import LovaszTheta.BranchingMomentRecursion
public import LovaszTheta.HermiteActivationTail

/-!
# Finite population moments

Induction on the moment order gives a constant bounding every
height truncation. The coefficient of the preceding height moment
is the mean offspring count, so a finite constant is preserved.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace LovaszTheta.Circulant.PlaneTree

private theorem exists_bound_heightPopulationMoment (p : ℕ → ℝ≥0∞)
    (hp : (∑' j, p j) = 1) {m : ℝ} (hm₀ : 0 ≤ m) (hm₁ : m < 1)
    (hm : (∑' j : ℕ, p j*(j : ℝ≥0∞)) = ENNReal.ofReal m)
    (hMom : ∀ r : ℕ, (∑' j : ℕ, p j*((j+1 : ℕ) : ℝ≥0∞)^r) ≠ ∞) (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ h, heightPopulationMoment p h r ≤ C := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    let B (s : Fin r) := (ih s.val s.isLt).choose
    have hB (s : Fin r) := (ih s.val s.isLt).choose_spec
    let L := 1+∑ s, B s
    have hL : 1 ≤ L := le_self_add
    have hLfin : L ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (ENNReal.sum_lt_top.mpr fun s _ ↦
        lt_top_iff_ne_top.mpr (hB s).1).ne⟩
    have hLow (h s : ℕ) (hs : s < r) : heightPopulationMoment p h s ≤ L := by
      have hSingle : B ⟨s,hs⟩ ≤ ∑ i, B i := single_le_sum (fun _ _ ↦ zero_le) (mem_univ (⟨s,hs⟩ : Fin r))
      exact ((hB ⟨s,hs⟩).2 h).trans (hSingle.trans le_add_self)
    let N := (∑' j : ℕ, p j*((j+1 : ℕ) : ℝ≥0∞)^r)*L^r
    have hN : N ≠ ∞ := ENNReal.mul_ne_top (hMom r) (ENNReal.pow_ne_top hLfin)
    let c := N.toReal/(1-m)
    let C := ENNReal.ofReal c
    have hden : 0 < 1-m := sub_pos.mpr hm₁
    have hc : 0 ≤ c := div_nonneg ENNReal.toReal_nonneg hden.le
    have hFix : ENNReal.ofReal m*C+N = C := by
      calc
        _ = ENNReal.ofReal m*ENNReal.ofReal c+ENNReal.ofReal N.toReal := by
          rw [ENNReal.ofReal_toReal hN]
        _ = ENNReal.ofReal (m*c+N.toReal) := by
          rw [← ENNReal.ofReal_mul hm₀, ← ENNReal.ofReal_add (mul_nonneg hm₀ hc) ENNReal.toReal_nonneg]
        _ = _ := by
          apply congrArg ENNReal.ofReal
          unfold c
          field_simp [hden.ne']
          ring
    refine ⟨C, ENNReal.ofReal_ne_top, fun h ↦ ?_⟩
    induction h with
    | zero => simp
    | succ h hPrev =>
      have hs := heightPopulationMoment_step_le hp h r hL (hLow h)
      rw [hm] at hs
      exact hs.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hPrev zero_le) N).trans_eq hFix)

private lemma summable_shifted_offspring_moment (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hMass : Summable a) (hMom : ∀ r : ℕ, Summable (fun j : ℕ ↦ (j : ℝ)^r*a j)) (r : ℕ) :
    Summable (fun j : ℕ ↦ a j * ((j : ℝ)+1)^r) := by
  have h := (hMass.add (hMom r)).mul_left ((2 : ℝ)^r)
  apply Summable.of_nonneg_of_le _ _ h
  · intro j
    exact mul_nonneg (ha j) (by positivity)
  · intro j
    have hQ : ((j : ℝ)+1)^r ≤ (2 : ℝ)^r * (1+(j : ℝ)^r) := by
      by_cases hj : j = 0
      · subst j
        simp only [Nat.cast_zero, zero_add, one_pow]
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (le_add_of_nonneg_right (by positivity))
      · have hJ : (1 : ℝ) ≤ j := by exact_mod_cast Nat.pos_of_ne_zero hj
        calc
          _ ≤ (2*(j : ℝ))^r := pow_le_pow_left₀ (by positivity) (by linarith) _
          _ = (2 : ℝ)^r*(j : ℝ)^r := mul_pow _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
    exact (mul_le_mul_of_nonneg_left hQ (ha j)).trans_eq (by ring)

/-- The population of a finite subcritical tree has finite moments,
provided the offspring law has moments at every order. -/
theorem tsum_weight_population_pow_ne_top (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hMass : HasSum a 1) {m : ℝ} (hm : HasSum (fun j : ℕ ↦ (j : ℝ)*a j) m) (hm₁ : m < 1)
    (hMom : ∀ r : ℕ, Summable (fun j : ℕ ↦ (j : ℝ)^r*a j)) (r : ℕ) :
    (∑' t : PlaneTree, weight (fun j ↦ ENNReal.ofReal (a j)) t * (population t : ℝ≥0∞)^r) ≠ ∞ := by
  let p (j : ℕ) := ENNReal.ofReal (a j)
  have hp : (∑' j, p j) = 1 := by
    unfold p
    rw [← ENNReal.ofReal_tsum_of_nonneg ha hMass.summable, hMass.tsum_eq, ENNReal.ofReal_one]
  have hm₀ : 0 ≤ m := by
    rw [← hm.tsum_eq]
    exact tsum_nonneg fun j ↦ mul_nonneg (by positivity) (ha j)
  have hMean : (∑' j : ℕ, p j*(j : ℝ≥0∞)) = ENNReal.ofReal m := by
    rw [← hm.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j ↦ mul_nonneg (by positivity) (ha j)) hm.summable]
    apply tsum_congr
    intro j
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_comm]
  have hShift (k : ℕ) : (∑' j : ℕ, p j*((j+1 : ℕ) : ℝ≥0∞)^k) ≠ ∞ := by
    have he (j : ℕ) : p j*((j+1 : ℕ) : ℝ≥0∞)^k =
        ENNReal.ofReal (a j*((j : ℝ)+1)^k) := by
      unfold p
      rw [ENNReal.ofReal_mul (ha j), ENNReal.ofReal_pow (by positivity)]
      rw [← Nat.cast_succ, ENNReal.ofReal_natCast]
    simp_rw [he]
    exact (summable_shifted_offspring_moment a ha hMass.summable hMom k).tsum_ofReal_ne_top
  obtain ⟨C, hC, hBound⟩ := exists_bound_heightPopulationMoment p hp hm₀ hm₁ hMean hShift r
  change (∑' t : PlaneTree, weight p t * (population t : ℝ≥0∞)^r) ≠ ∞
  rw [← iSup_heightPopulationMoment p r]
  exact (lt_of_le_of_lt (iSup_le hBound) (lt_top_iff_ne_top.mpr hC)).ne

/-- The population tail is bounded by the population moment
divided by the cutoff to that power. -/
theorem weight_population_tail_le (p : ℕ → ℝ≥0∞) {D : ℕ} (hD : 0 < D) (r : ℕ) :
    (∑' t : PlaneTree, if D < population t then weight p t else 0) ≤
      (∑' t : PlaneTree, weight p t * (population t : ℝ≥0∞)^r) / (D : ℝ≥0∞)^r := by
  rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_le_tsum
  intro t
  change (if D < population t then weight p t else 0) ≤ _
  by_cases ht : D < population t
  · rw [ite_eq_left ht]
    have he : (D : ℝ≥0∞)^r * ((D : ℝ≥0∞)^r)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by positivity) (by finiteness)
    calc
      _ = (weight p t*(D : ℝ≥0∞)^r)*((D : ℝ≥0∞)^r)⁻¹ := by rw [mul_assoc, he, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ zero_le (by exact_mod_cast ht.le) _) zero_le) zero_le
  · rw [ite_eq_right ht]
    exact zero_le

/-- The Gaussian offspring probabilities give a probability law
on finite ordered trees with finite population moments. -/
theorem gaussian_weight_mass_and_population_moments {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    let p (j : ℕ) := ENNReal.ofReal (gaussianOffspringProbability τ σ j)
    (∑' t : PlaneTree, weight p t) = 1 ∧
      ∀ r : ℕ, (∑' t : PlaneTree, weight p t * (population t : ℝ≥0∞)^r) ≠ ∞ := by
  obtain ⟨hM, m, hm, hm₁⟩ := gaussianOffspringProbability_mass_and_mean hτ hσ hMean
  exact ⟨tsum_weight_eq_one_of_subcritical _ (gaussianOffspringProbability_nonneg τ σ) hM hm hm₁,
    tsum_weight_population_pow_ne_top _ (gaussianOffspringProbability_nonneg τ σ) hM hm hm₁
      (summable_gaussianOffspringProbability_moment hτ hσ hσ' hMean)⟩

end LovaszTheta.Circulant.PlaneTree
