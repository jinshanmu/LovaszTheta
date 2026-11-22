module

public import LovaszTheta.Projections

/-!
# The smoothed equation and upper bound for the circulant model

The barrier minimizer lies in the connection kernel. Its positive
coordinatewise reciprocal, weighted by the smoothing weights, lies in
the complementary kernel. These factors give the exact smoothed
equation and the logarithmic residual bound.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The smoothing weights are one at zero and τ/n at every other frequency. -/
noncomputable def weight (n : ℕ) (τ : ℝ) (i : ZMod n) : ℝ :=
  if i = 0 then 1 else τ / n

omit [NeZero n] in
@[simp]
lemma weight_zero (τ : ℝ) : weight n τ 0 = 1 := by simp [weight]

lemma weight_pos {τ : ℝ} (hτ : 0 < τ) (i : ZMod n) : 0 < weight n τ i := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold weight
  split_ifs <;> positivity

omit [NeZero n] in
lemma weight_even (τ : ℝ) : (weight n τ).Even := by
  intro i
  simp [weight]

/-- The real even part of the kernel of a Fourier projection. -/
noncomputable def evenKernel (S : Set (ZMod n)) : Submodule ℝ (ZMod n → ℝ) where
  carrier := {v | v.Even ∧ realProjection S *ᵥ v = 0}
  zero_mem' := ⟨fun _ ↦ rfl, Matrix.mulVec_zero _⟩
  add_mem' := fun ⟨hx, hX⟩ ⟨hy, hY⟩ ↦
    ⟨fun i ↦ by simp only [Pi.add_apply, hx i, hy i], by rw [Matrix.mulVec_add, hX, hY, zero_add]⟩
  smul_mem' := fun a _ ⟨hv, hV⟩ ↦
    ⟨fun i ↦ by simp only [Pi.smul_apply, hv i], by rw [Matrix.mulVec_smul, hV, smul_zero]⟩

private lemma projection_zero_of_disjoint {S T : Set (ZMod n)} (hS : ∀ s, -s ∈ S ↔ s ∈ S)
    (hT : ∀ s, -s ∈ T ↔ s ∈ T) (hST : Disjoint S T) (v : ZMod n → ℝ) :
    realProjection S *ᵥ (realProjection T *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, realProjection_mul_of_disjoint hS hT hST, Matrix.zero_mulVec]

private lemma one_mem_connection_kernel (x : InversionClass n → Bool) :
    (1 : ZMod n → ℝ) ∈ evenKernel (connectionSet x) := by
  have h0 : meanVector (1 : ZMod n → ℝ) = 1 := by
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    funext i
    simp [meanVector, mass, ZMod.card, hn]
  refine ⟨fun _ ↦ rfl, ?_⟩
  calc
    realProjection (connectionSet x) *ᵥ (1 : ZMod n → ℝ) =
        realProjection (connectionSet x) *ᵥ (realProjection {0} *ᵥ (1 : ZMod n → ℝ)) := by
      rw [realProjection_zero_mulVec, h0]
    _ = 0 := projection_zero_of_disjoint (connectionSet_even x) zeroSet_even
      (connection_zero_disjoint x) _

private lemma projected_nonconnection_mass_zero (x : InversionClass n → Bool) (q : ZMod n → ℝ) :
    mass (realProjection (nonconnectionSet x) *ᵥ q) = 0 := by
  have hz := projection_zero_of_disjoint zeroSet_even (nonconnectionSet_even x)
    (nonconnection_zero_disjoint x).symm q
  rw [realProjection_zero_mulVec] at hz
  have hEval := congrFun hz 0
  change mass (realProjection (nonconnectionSet x) *ᵥ q) / Fintype.card (ZMod n) = 0 at hEval
  have hn : (Fintype.card (ZMod n) : ℝ) ≠ 0 := by
    rw [ZMod.card]
    exact_mod_cast NeZero.ne n
  exact (div_eq_zero_iff.mp hEval).resolve_right hn

private lemma nonconnection_projection_eval (x : InversionClass n → Bool) {q : ZMod n → ℝ}
    (hqEven : q.Even) {c : ℝ}
    (hStat : ∀ v ∈ evenKernel (connectionSet x), (q ⬝ᵥ v) = c * mass v) :
    realProjection (nonconnectionSet x) *ᵥ q = 0 := by
  let N := realProjection (nonconnectionSet x)
  let y := N *ᵥ q
  have hy : y ∈ evenKernel (connectionSet x) :=
    ⟨realProjection_even _ hqEven, projection_zero_of_disjoint (connectionSet_even x)
      (nonconnectionSet_even x) (connection_nonconnection_disjoint x) q⟩
  have hyMass : mass y = 0 := projected_nonconnection_mass_zero x q
  have hyy : N *ᵥ y = y := by
    change realProjection (nonconnectionSet x) *ᵥ (realProjection (nonconnectionSet x) *ᵥ q) = _
    rw [Matrix.mulVec_mulVec, realProjection_idempotent _ (nonconnectionSet_even x)]
  have hDot : y ⬝ᵥ y = 0 := by
    calc
      y ⬝ᵥ y = q ⬝ᵥ (N *ᵥ y) := realProjection_selfAdjoint _ _ _
      _ = _ := by rw [hyy, hStat y hy, hyMass, mul_zero]
  exact dotProduct_star_self_eq_zero.mp (by simpa only [star_trivial] using hDot)

private lemma signOperator_factors (x : InversionClass n → Bool) {p q : ZMod n → ℝ}
    (hP : realProjection (connectionSet x) *ᵥ p = 0)
    (hQ : realProjection (nonconnectionSet x) *ᵥ q = 0)
    (hMass : mass p = mass q) :
    signOperator x (p + q) = p - q := by
  have hSum (v : ZMod n → ℝ) :
      realProjection (connectionSet x) *ᵥ v + realProjection (nonconnectionSet x) *ᵥ v +
        meanVector v = v := by
    rw [← realProjection_zero_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
      real_projection_sum, Matrix.one_mulVec]
  have hP' := hSum p
  have hQ' := hSum q
  rw [hP, zero_add, ← eq_sub_iff_add_eq] at hP'
  rw [hQ, add_zero, ← eq_sub_iff_add_eq] at hQ'
  have hM : meanVector p = meanVector q :=
    congrArg (fun a : ℝ ↦ fun _ : ZMod n ↦ a / Fintype.card (ZMod n)) hMass
  rw [signOperator_apply, Matrix.mulVec_add, Matrix.mulVec_add, hP, hQ, add_zero, zero_add,
    hP', hQ', hM]
  abel

/-- Positive factors in the two kernels solve the exact equation and give the
barrier upper bound for theta. -/
theorem exists_smoothed_factors (x : InversionClass n → Bool) {τ : ℝ} (hτ : 0 < τ) :
    ∃ p ∈ evenKernel (connectionSet x), ∃ q ∈ evenKernel (nonconnectionSet x),
      (∀ i, 0 < p i ∧ 0 < q i ∧ p i * q i = weight n τ i) ∧
      mass p = Real.sqrt (n * mass (weight n τ)) ∧
      mass q = Real.sqrt (n * mass (weight n τ)) ∧
      signOperator x (p + q) = p - q ∧
      theta (graph x) / Real.sqrt n ≤ Real.sqrt (mass (weight n τ)) * p 0 := by
  obtain ⟨p, hp, q, hPos, hpM, hqM, hStat⟩ := exists_barrier_factors
    (weight_pos hτ) (evenKernel (connectionSet x)) (one_mem_connection_kernel x)
  have hpEven : p.Even := hp.1
  have hqReal (i : ZMod n) : q i = weight n τ i / p i :=
    (eq_div_iff (hPos i).1.ne').mpr (by rw [mul_comm]; exact (hPos i).2.2)
  have hqEven : q.Even := by
    intro i
    rw [hqReal (-i), hqReal i, weight_even, hpEven]
  have hQ : realProjection (nonconnectionSet x) *ᵥ q = 0 :=
    nonconnection_projection_eval x hqEven hStat
  have hFixed := signOperator_factors x hp.2 hQ (hpM.trans hqM.symm)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨y, hy, hyMax, _⟩ := theta_isMax_fourier x
  have hyU : y ∈ evenKernel (connectionSet x) := ⟨hy.1,
    (realProjection_mulVec_eq_zero_iff _ (connectionSet_even x) y).mpr hy.2.2.2⟩
  have hDot : (∑ i, q i * y i) = mass p / n := by
    simpa only [hy.2.2.1, mul_one, ZMod.card] using hStat y hyU
  have hZero : q 0 * y 0 ≤ mass p / n := by
    rw [← hDot]
    exact Finset.single_le_sum (fun i _ ↦ mul_nonneg (hPos i).2.1.le (hy.2.1 i)) (mem_univ 0)
  have hΘ : theta (graph x) * q 0 ≤ mass p := by
    rw [← hyMax]
    calc
      (n * y 0) * q 0 = q 0 * y 0 * n := by ring
      _ ≤ _ := (le_div_iff₀ hn).mp hZero
  have hpq0 : q 0 * p 0 = 1 := by rw [mul_comm, (hPos 0).2.2, weight_zero]
  have hΘ' := mul_le_mul_of_nonneg_right hΘ (hPos 0).1.le
  rw [mul_assoc, hpq0, mul_one] at hΘ'
  have hpMn : mass p = Real.sqrt (n * mass (weight n τ)) := by
    simpa only [ZMod.card] using hpM
  have hBound : theta (graph x) / Real.sqrt n ≤ Real.sqrt (mass (weight n τ)) * p 0 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
    rw [hpMn, Real.sqrt_mul hn.le] at hΘ'
    simpa only [mul_comm (Real.sqrt (n : ℝ)), mul_assoc] using hΘ'
  exact ⟨p, hp, q, ⟨hqEven, hQ⟩, hPos, hpMn, by simpa only [ZMod.card] using hqM, hFixed, hBound⟩

/-- The residual and logarithmic bounds for the same factors supplied by
the smoothed Fourier program. -/
theorem theta_residual_bound_of_factors (x : InversionClass n → Bool) {τ : ℝ} (hτ : 0 < τ)
    {p q : ZMod n → ℝ} (hPos : ∀ i, 0 < p i ∧ 0 < q i ∧ p i * q i = weight n τ i)
    (hpM : mass p = Real.sqrt (n * mass (weight n τ)))
    (hqM : mass q = Real.sqrt (n * mass (weight n τ)))
    (hFixed : signOperator x (p + q) = p - q)
    (hUpper : theta (graph x) / Real.sqrt n ≤ Real.sqrt (mass (weight n τ)) * p 0)
    (v : ZMod n → ℝ) :
    0 ≤ discrepancy (weight n τ) p v ∧
    discrepancy (weight n τ) p v ≤ (norm₂ v + norm₂ (p - q) / 2) *
      norm₂ (v - signOperator x (smooth (weight n τ) v)) ∧
    Real.log (theta (graph x) / Real.sqrt n) ≤
      Real.log (mass (weight n τ)) / 2 + |v 0| / 2 + Real.sqrt (discrepancy (weight n τ) p v) := by
  have hp (i : ZMod n) := (hPos i).1
  have hpq (i : ZMod n) := (hPos i).2.2
  have hΘ : 0 < theta (graph x) / Real.sqrt n :=
    div_pos (zero_lt_one.trans_le (one_le_theta _)) (Real.sqrt_pos_of_pos (by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)))
  refine ⟨discrepancy_nonneg (weight_pos hτ) hp, ?_, ?_⟩
  · apply discrepancy_le_residual (signOperator x) (signOperator_selfAdjoint x) (signOperator_square x)
      (weight_pos hτ) hp hpq _ _ hFixed
    · simpa only [ZMod.card] using hpM
    · simpa only [ZMod.card] using hqM
  · exact log_bound_of_discrepancy (weight_pos hτ) hp 0 (weight_zero τ) hΘ hUpper

/-- The smoothed Fourier equation is stable in the sense of the residual estimate,
including its logarithmic upper bound for theta. -/
theorem exists_theta_residual_bound (x : InversionClass n → Bool) {τ : ℝ} (hτ : 0 < τ) :
    ∃ p q : ZMod n → ℝ, signOperator x (smooth (weight n τ) (p - q)) = p - q ∧
      ∀ v : ZMod n → ℝ,
        0 ≤ discrepancy (weight n τ) p v ∧
        discrepancy (weight n τ) p v ≤ (norm₂ v + norm₂ (p - q) / 2) *
          norm₂ (v - signOperator x (smooth (weight n τ) v)) ∧
        Real.log (theta (graph x) / Real.sqrt n) ≤
          Real.log (mass (weight n τ)) / 2 + |v 0| / 2 +
            Real.sqrt (discrepancy (weight n τ) p v) := by
  obtain ⟨p, _, q, _, hPos, hpM, hqM, hFixed, hUpper⟩ := exists_smoothed_factors x hτ
  refine ⟨p, q, ?_, theta_residual_bound_of_factors x hτ hPos hpM hqM hFixed hUpper⟩
  rw [smooth_exact_difference (fun i ↦ (hPos i).1) (fun i ↦ (hPos i).2.1)
    (fun i ↦ (hPos i).2.2), hFixed]

end LovaszTheta.Circulant
