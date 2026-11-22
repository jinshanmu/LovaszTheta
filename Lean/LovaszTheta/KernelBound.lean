module

public import LovaszTheta.Expectation
public import LovaszTheta.KernelChaining

/-!
# The Fourier kernel bound and the smoothed factors

When the Fourier transform of a unit vector vanishes on either of the two
residue sets, the absolute value of the process is one minus the zero-mode
mass. This excludes such vectors from the small ℓ¹ ball on the chaining
event. Apply the resulting inequality to the positive factors in the two
real even kernels.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma sum_fourierReal_sq (x : ZMod n → ℝ) :
    (∑ i, ‖fourierReal x i‖ ^ 2) = (n : ℝ) * ∑ i, x i ^ 2 := by
  simpa only [fourierReal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    sum_norm_dft_sq (fun i ↦ (x i : ℂ))

omit [NeZero n] in
private lemma epsilon_cases (signs : InversionClass n → Bool) {a : ZMod n} (ha : a ≠ 0) :
    epsilon signs a = -1 ∨ epsilon signs a = 1 := by
  cases e : signs (inversionClass a ha) <;> simp [epsilon, ha, e]

private lemma realKernelProcess_eq_of_mask (signs : InversionClass n → Bool)
    (x : ZMod n → ℝ) (hx : ∑ i, x i ^ 2 = 1) {σ : ℝ}
    (hMask : ∀ i, i ≠ 0 → epsilon signs i ≠ σ → fourierReal x i = 0) :
    realKernelProcess signs x = σ * (1 - ‖fourierReal x 0‖ ^ 2 / n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let h (i : ZMod n) : ℝ := ‖fourierReal x i‖ ^ 2
  have hSum : (∑ i ∈ univ.erase 0, h i) = (n : ℝ) - h 0 := by
    have he := sum_erase_add univ h (mem_univ 0)
    change (∑ i ∈ univ.erase 0, h i) + h 0 = ∑ i, ‖fourierReal x i‖ ^ 2 at he
    rw [sum_fourierReal_sq, hx, mul_one] at he
    linarith
  have hEqual : (∑ i ∈ univ.erase 0, epsilon signs i * h i) =
      ∑ i ∈ univ.erase 0, σ * h i := by
    apply sum_congr rfl
    intro i hi
    by_cases hs : epsilon signs i = σ
    · rw [hs]
    · have hz := hMask i (mem_erase.mp hi).1 hs
      simp [h, hz]
  change (∑ i, epsilon signs i * h i) / n = σ * (1 - h 0 / n)
  rw [← sum_erase_add univ (fun i ↦ epsilon signs i * h i) (mem_univ 0),
    epsilon_zero, zero_mul, add_zero, hEqual, ← mul_sum, hSum]
  field_simp

/-- The good event in the kernel lemma controls both null spaces at once. -/
def kernelControl (signs : InversionClass n → Bool) : Prop :=
  ∀ x : ZMod n → ℝ, ((∀ i ∈ connectionSet signs, fourierReal x i = 0) ∨
      (∀ i ∈ nonconnectionSet signs, fourierReal x i = 0)) →
    norm₂ x ≤ ellOne x / kernelRadius n

private lemma kernelControl_of_small_process (hn : 1 ≤ n)
    (signs : InversionClass n → Bool)
    (hSmall : ∀ y ∈ kernelBall (n := n) (kernelRadius n),
      |realKernelProcess signs y| ≤ 1 / 2) :
    kernelControl signs := by
  let R := kernelRadius n
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_one.trans_le hn
  have hL := kernelLog_one_le hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hLsq : 1 ≤ kernelLog n ^ 2 := by nlinarith [sq_nonneg (kernelLog n - 1)]
  have hDen : 0 < 65536 * kernelLog n ^ 2 := by positivity
  have hR : 0 < R := div_pos hs hDen
  have hRs : R ≤ Real.sqrt (n : ℝ) / 2 := by
    change Real.sqrt (n : ℝ) / (65536 * kernelLog n ^ 2) ≤ Real.sqrt (n : ℝ) / 2
    exact div_le_div_of_nonneg_left hs.le (by norm_num) (by linarith)
  have hRratio : R ^ 2 / (n : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ (Real.sqrt (n : ℝ) / 2) ^ 2 := pow_le_pow_left₀ hR.le hRs _
      _ = _ := by rw [div_pow, Real.sq_sqrt hnR.le]; ring
  intro x hx
  change norm₂ x ≤ ellOne x / R
  by_contra! hNot
  have hEll : 0 ≤ ellOne x := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hX : 0 < norm₂ x := (div_nonneg hEll hR.le).trans_lt hNot
  let y := (norm₂ x)⁻¹ • x
  have hyUnit : (∑ i, y i ^ 2) = 1 := by
    have hSq : (∑ i, x i ^ 2) = norm₂ x ^ 2 := by
      simpa only [dotProduct, pow_two] using (norm₂_sq x).symm
    simp only [y, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← mul_sum, hSq, ← mul_pow, inv_mul_cancel₀ hX.ne', one_pow]
  have hyEll : ellOne y ≤ R := by
    have hNorm := (div_lt_iff₀ hR).mp hNot
    have hDiv : (norm₂ x)⁻¹ * ellOne x ≤ R := by
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ hX).mpr
      linarith
    simpa only [ellOne, y, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hX), ← mul_sum] using hDiv
  have hyLow : (1 / 2 : ℝ) < 1 - ‖fourierReal y 0‖ ^ 2 / n := by
    have hNorm := (norm_fourierReal_le_ellOne y 0).trans hyEll
    have hPow := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    have hRat := (div_le_div_of_nonneg_right hPow hnR.le).trans hRratio
    linarith
  have hYzero (i : ZMod n) (hi : fourierReal x i = 0) : fourierReal y i = 0 := by
    simp [y, map_smul, hi]
  have hyBound := hSmall y ⟨hyUnit.le, hyEll⟩
  rcases hx with hc | hc
  · have hEq := realKernelProcess_eq_of_mask signs y hyUnit (σ := 1) (fun i hi hne ↦
      hYzero i (hc i ((epsilon_cases signs hi).resolve_right hne)))
    rw [hEq, one_mul, abs_of_pos (by linarith)] at hyBound
    linarith
  · have hEq := realKernelProcess_eq_of_mask signs y hyUnit (σ := -1) (fun i hi hne ↦
      hYzero i (hc i ((epsilon_cases signs hi).resolve_left hne)))
    rw [hEq, neg_one_mul, abs_neg, abs_of_pos (by linarith)] at hyBound
    linarith

/-- Fourier kernel inequality for every real vector, with a simultaneous
failure bound for the connection and nonconnection sets. -/
theorem probability_kernelControl_failure (hn : 1 ≤ n) :
    probability (fun signs : InversionClass n → Bool ↦ ¬kernelControl signs) ≤
      4 * Real.exp (-(kernelLog n ^ 2)) := by
  apply (probability_mono (q := fun signs ↦ ∃ x ∈ kernelBall (n := n) (kernelRadius n),
    (1 / 2 : ℝ) < |realKernelProcess signs x|) ?_).trans (probability_kernelBall_large hn)
  intro signs h
  by_contra! hSmall
  exact h (kernelControl_of_small_process hn signs hSmall)

/-- On even real vectors, the forward Fourier transform describes the kernel
of the real Fourier projection. -/
lemma fourierReal_eq_zero_of_mem_evenKernel {S : Set (ZMod n)} (hS : ∀ i, -i ∈ S ↔ i ∈ S)
    {x : ZMod n → ℝ} (hx : x ∈ evenKernel S) {i : ZMod n} (hi : i ∈ S) :
    fourierReal x i = 0 := by
  have hz := (fourierProjection_mulVec_eq_zero_iff S _).mp
    ((realProjection_mulVec_eq_zero_iff S hS x).mp hx.2) (-i) ((hS i).mpr hi)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [fourierMatrix_conjTranspose_mulVec, Pi.smul_apply, ZMod.invDFT_apply',
    neg_neg, smul_smul, mul_inv_cancel₀ hn, one_smul] at hz
  exact hz

private lemma norm₂_sub_le (x y : ZMod n → ℝ) : norm₂ (x - y) ≤ norm₂ x + norm₂ y := by
  have hDot := (abs_le.mp (abs_dotProduct_le x y)).1
  have hSq : norm₂ (x - y) ^ 2 ≤ (norm₂ x + norm₂ y) ^ 2 := by
    rw [norm₂_sq, sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm y x,
      ← norm₂_sq, ← norm₂_sq]
    linarith only [hDot]
  exact le_of_pow_le_pow_left₀ (by positivity : 2 ≠ (0 : ℕ))
    (add_nonneg (norm₂_nonneg _) (norm₂_nonneg _)) hSq

/-- The bound on the norm of the exact solution \(f=p-q\) in terms of the
two factor masses on the kernel event. -/
theorem norm₂_factor_sub_le (hn : 1 ≤ n) (signs : InversionClass n → Bool)
    (h : kernelControl signs) {τ : ℝ} (hτ : 0 < τ) {p q : ZMod n → ℝ}
    (hp : p ∈ evenKernel (connectionSet signs)) (hq : q ∈ evenKernel (nonconnectionSet signs))
    (hPos : ∀ i, 0 ≤ p i ∧ 0 ≤ q i)
    (hpM : mass p = Real.sqrt (n * mass (weight n τ)))
    (hqM : mass q = Real.sqrt (n * mass (weight n τ))) :
    norm₂ (p - q) ≤ 131072 * Real.sqrt (1 + τ) * kernelLog n ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hL : 0 < kernelLog n := zero_lt_one.trans_le (kernelLog_one_le hn)
  have hR : 0 < kernelRadius n := by unfold kernelRadius; positivity
  have hpEll : ellOne p = mass p := sum_congr rfl fun i _ ↦ abs_of_nonneg (hPos i).1
  have hqEll : ellOne q = mass q := sum_congr rfl fun i _ ↦ abs_of_nonneg (hPos i).2
  have hpB := h p (.inl (fun i hi ↦
    fourierReal_eq_zero_of_mem_evenKernel (connectionSet_even signs) hp hi))
  have hqB := h q (.inr (fun i hi ↦
    fourierReal_eq_zero_of_mem_evenKernel (nonconnectionSet_even signs) hq hi))
  have hW := Real.sqrt_le_sqrt (mass_weight_le hτ.le : mass (weight n τ) ≤ 1 + τ)
  have hM : Real.sqrt (n * mass (weight n τ)) / kernelRadius n ≤
      65536 * Real.sqrt (1 + τ) * kernelLog n ^ 2 := by
    calc
      _ ≤ (Real.sqrt (n : ℝ) * Real.sqrt (1 + τ)) / kernelRadius n := by
        rw [Real.sqrt_mul hnR.le]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW hs.le) hR.le
      _ = _ := by unfold kernelRadius; field_simp
  rw [hpEll, hpM] at hpB
  rw [hqEll, hqM] at hqB
  have hTri := norm₂_sub_le p q
  linarith only [hpB.trans hM, hqB.trans hM, hTri]

end LovaszTheta.Circulant
