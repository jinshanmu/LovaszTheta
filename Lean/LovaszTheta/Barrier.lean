module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic

/-!
# The logarithmic barrier for the Fourier program

This file proves the existence and first-order equations of the positive
barrier factors in the smoothed Fourier program. The primal subspace is
a finite-dimensional real subspace containing the constant vector.
-/

@[expose] public section

open Finset Set Filter
open scoped Topology

namespace LovaszTheta.Circulant

variable {V : Type*} [Fintype V]

/-- The mass of a vector, with counting measure on its coordinates. -/
def mass (x : V → ℝ) : ℝ := ∑ i, x i

lemma mass_add (x y : V → ℝ) : mass (x + y) = mass x + mass y := by
  simp [mass, sum_add_distrib]

lemma mass_smul (s : ℝ) (x : V → ℝ) : mass (s • x) = s * mass x := by
  simp [mass, mul_sum]

private lemma mass_pos [Nonempty V] {x : V → ℝ} (hx : ∀ i, 0 < x i) : 0 < mass x :=
  sum_pos (fun i _ ↦ hx i) univ_nonempty

private lemma le_mass {x : V → ℝ} (hx : ∀ i, 0 ≤ x i) (i : V) : x i ≤ mass x :=
  Finset.single_le_sum (fun j _ ↦ hx j) (mem_univ i)

/-- The function minimized to obtain the two positive Fourier vectors. -/
noncomputable def barrier (w x : V → ℝ) : ℝ :=
  (mass x) ^ 2 / (2 * Fintype.card V) - ∑ i, w i * Real.log (x i)

private lemma barrier_sublevel_box [Nonempty V] {w : V → ℝ} (hw : ∀ i, 0 < w i) (B : ℝ) :
    ∃ R : ℝ, ∃ m : V → ℝ, (∀ i, 0 < m i) ∧
      ∀ x, (∀ i, 0 < x i) → barrier w x ≤ B → ∀ i, x i ∈ Icc (m i) R := by
  classical
  let N : ℝ := Fintype.card V
  let ω := mass w
  have hN : 0 < N := by dsimp [N]; positivity
  have hω : 0 < ω := mass_pos hw
  let R := max 1 (2 * N * (ω + |B|))
  have hR : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  let m (i : V) := Real.exp (-(B + ω * R) / w i)
  refine ⟨R, m, fun i ↦ Real.exp_pos _, fun x hx hBx i ↦ ?_⟩
  let S := mass x
  have hS : 0 < S := mass_pos hx
  have hix (j : V) : x j ≤ S := le_mass (fun j ↦ (hx j).le) j
  have hLogSum : (∑ j, w j * Real.log (x j)) ≤ ω * S := by
    unfold ω mass
    rw [Finset.sum_mul]
    exact sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
      ((Real.log_le_self (hx j).le).trans (hix j)) (hw j).le
  have hSq : S ^ 2 / (2 * N) ≤ B + ω * S := by
    change S ^ 2 / (2 * N) - _ ≤ B at hBx
    linarith
  have hSR : S ≤ R := by
    by_cases hS₁ : S ≤ 1
    · exact hS₁.trans (le_max_left _ _)
    · have hB : B ≤ |B| * S :=
        (le_abs_self B).trans (le_mul_of_one_le_right (abs_nonneg B) (le_of_not_ge hS₁))
      have h' : S ^ 2 ≤ (2 * N * (ω + |B|)) * S := by
        calc
          S ^ 2 ≤ (B + ω * S) * (2 * N) := (div_le_iff₀ (by positivity)).mp hSq
          _ ≤ (|B| * S + ω * S) * (2 * N) :=
            mul_le_mul_of_nonneg_right (by linarith only [hB]) (by positivity)
          _ = _ := by ring
      exact ((mul_le_mul_iff_left₀ hS).mp (by simpa only [pow_two, mul_comm S] using h')).trans
        (le_max_right _ _)
  have hOther : (∑ j ∈ univ.erase i, w j * Real.log (x j)) ≤ ω * R := by
    calc
      _ ≤ ∑ j ∈ univ.erase i, w j * R :=
        sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
          ((Real.log_le_self (hx j).le).trans ((hix j).trans hSR)) (hw j).le
      _ ≤ ∑ j, w j * R :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun j _ _ ↦ mul_nonneg (hw j).le hR
      _ = ω * R := (Finset.sum_mul _ _ _).symm
  have hLowerLog : -(B + ω * R) ≤ w i * Real.log (x i) := by
    change S ^ 2 / (2 * N) - _ ≤ B at hBx
    rw [← sum_erase_add _ _ (mem_univ i)] at hBx
    have : 0 ≤ S ^ 2 / (2 * N) := by positivity
    linarith
  refine ⟨?_, (hix i).trans hSR⟩
  dsimp [m]
  rw [← Real.le_log_iff_exp_le (hx i)]
  exact (div_le_iff₀ (hw i)).mpr (by simpa only [mul_comm (Real.log (x i))] using hLowerLog)

/-- The barrier attains its minimum over positive vectors in the primal subspace. -/
theorem exists_barrier_minimizer [Nonempty V]
    {w : V → ℝ} (hw : ∀ i, 0 < w i) (U : Submodule ℝ (V → ℝ))
    (hOne : (1 : V → ℝ) ∈ U) :
    ∃ p ∈ U, (∀ i, 0 < p i) ∧
      ∀ q ∈ U, (∀ i, 0 < q i) → barrier w p ≤ barrier w q := by
  let B := barrier w 1
  obtain ⟨R, m, hm, hBox⟩ := barrier_sublevel_box hw B
  let A : Set (V → ℝ) := Set.pi univ (fun i ↦ Icc (m i) R) ∩ (U : Set (V → ℝ))
  have hCompact : IsCompact A :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).inter_right U.isClosed_of_finiteDimensional
  have h1 : (1 : V → ℝ) ∈ A := ⟨fun i _ ↦ hBox 1 (fun _ ↦ zero_lt_one) le_rfl i, hOne⟩
  have hPos {x : V → ℝ} (hx : x ∈ A) (i : V) : 0 < x i :=
    (hm i).trans_le (hx.1 i (mem_univ i)).1
  have hcont : ContinuousOn (barrier w) A := by
    unfold barrier mass
    have hv (i : V) : Continuous (fun x : V → ℝ ↦ x i) := continuous_apply i
    have hl (i : V) : ContinuousOn (fun x : V → ℝ ↦ Real.log (x i)) A :=
      (hv i).continuousOn.log fun x hx ↦ (hPos hx i).ne'
    fun_prop
  obtain ⟨p, hp, hmin⟩ := hCompact.exists_isMinOn ⟨1, h1⟩ hcont
  refine ⟨p, hp.2, hPos hp, fun q hq hqPos ↦ ?_⟩
  by_cases hqB : barrier w q ≤ B
  · exact hmin ⟨fun i _ ↦ hBox q hqPos hqB i, hq⟩
  · exact (hmin h1).trans (le_of_not_ge hqB)

private lemma barrier_first_order
    {w p : V → ℝ} {U : Submodule ℝ (V → ℝ)} (hpU : p ∈ U) (hp : ∀ i, 0 < p i)
    (hmin : ∀ x ∈ U, (∀ i, 0 < x i) → barrier w p ≤ barrier w x) {v : V → ℝ}
    (hv : v ∈ U) :
    (∑ i, (w i / p i) * v i) = mass p / Fintype.card V * mass v := by
  let f (t : ℝ) := barrier w (p + t • v)
  have hLine (i : V) : HasDerivAt (fun t : ℝ ↦ p i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i)
  have hMass : HasDerivAt (fun t : ℝ ↦ mass (p + t • v)) (mass v) 0 := by
    unfold mass
    exact HasDerivAt.fun_sum fun i _ ↦ hLine i
  have hLog (i : V) :
      HasDerivAt (fun t : ℝ ↦ w i * Real.log (p i + t * v i)) ((w i / p i) * v i) 0 := by
    have hp' : p i + (0 : ℝ) * v i ≠ 0 := by simpa using (hp i).ne'
    have h := ((Real.hasDerivAt_log hp').comp 0 (hLine i)).const_mul (w i)
    simpa only [Function.comp_apply, zero_mul, add_zero, div_eq_mul_inv, mul_assoc] using h
  have hD : HasDerivAt f
      (mass p / Fintype.card V * mass v - ∑ i, (w i / p i) * v i) 0 := by
    have hSq := (hMass.pow 2).div_const (2 * (Fintype.card V : ℝ))
    have hSum := HasDerivAt.fun_sum (u := univ) fun i _ ↦ hLog i
    convert hSq.sub hSum using 1
    · rfl
    · norm_num
      ring
  have hPos : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < (p + t • v) i := by
    refine eventually_all.mpr fun i ↦ ?_
    have hAt : 0 < p i + (0 : ℝ) * v i := by simpa using hp i
    exact (hLine i).continuousAt.eventually_const_lt hAt
  have hLocal : IsLocalMin f 0 := by
    filter_upwards [hPos] with t ht
    simpa [f] using hmin (p + t • v) (U.add_mem hpU (U.smul_mem t hv)) ht
  linarith [hLocal.hasDerivAt_eq_zero hD]

/-- The positive solutions have equal masses and their coordinatewise product is the weight. -/
theorem exists_barrier_factors [Nonempty V]
    {w : V → ℝ} (hw : ∀ i, 0 < w i) (U : Submodule ℝ (V → ℝ))
    (hOne : (1 : V → ℝ) ∈ U) :
    ∃ p ∈ U, ∃ q : V → ℝ, (∀ i, 0 < p i ∧ 0 < q i ∧ p i * q i = w i) ∧
      mass p = Real.sqrt (Fintype.card V * mass w) ∧
      mass q = Real.sqrt (Fintype.card V * mass w) ∧
      ∀ v ∈ U, ∑ i, q i * v i = mass p / Fintype.card V * mass v := by
  obtain ⟨p, hpU, hp, hmin⟩ := exists_barrier_minimizer hw U hOne
  let q (i : V) := w i / p i
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; positivity
  have hstat (v : V → ℝ) (hv : v ∈ U) :
      (∑ i, q i * v i) = mass p / N * mass v := barrier_first_order hpU hp hmin hv
  have hprod (i : V) : p i * q i = w i := by
    rw [mul_comm]
    exact div_mul_cancel₀ (w i) (hp i).ne'
  have hpSq : (mass p) ^ 2 = N * mass w := by
    have h := hstat p hpU
    simp_rw [mul_comm (q _) (p _), hprod] at h
    change mass w = mass p / N * mass p at h
    field_simp at h
    linear_combination -h
  have hpMass : mass p = Real.sqrt (N * mass w) := by
    rw [← hpSq, Real.sqrt_sq (mass_pos hp).le]
  have hqMass : mass q = mass p := by
    have h := hstat 1 hOne
    simpa [mass, N, div_mul_cancel₀ _ hN.ne'] using h
  exact ⟨p, hpU, q, fun i ↦ ⟨hp i, div_pos (hw i) (hp i), hprod i⟩, hpMass,
    hqMass.trans hpMass, hstat⟩

end LovaszTheta.Circulant
