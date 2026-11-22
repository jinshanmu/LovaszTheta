module

public import LovaszTheta.SharpMoment
public import LovaszTheta.RoughNorm

/-!
# The sharp graph-matrix norm bound

Apply the even trace moment at twice the ceiling of the squared logarithm.
The defect ratio vanishes and Markov's inequality gives failure probability
smaller than every fixed inverse power of the vertex count.
-/

@[expose] public section

open Finset Matrix Filter
open scoped Classical Matrix Matrix.Norms.L2Operator Topology

namespace LovaszTheta.Independent

private noncomputable def sharpPowerHalf (n : ℕ) : ℕ := max 1 ⌈(Real.log (n : ℝ))^2⌉₊

private noncomputable def sharpOffset (n : ℕ) : ℕ := 2*sharpPowerHalf n-2

private lemma sharpOffset_add_two (n : ℕ) : sharpOffset n+2 = 2*sharpPowerHalf n := by
  have h : 1 ≤ sharpPowerHalf n := le_max_left _ _
  unfold sharpOffset
  omega

private lemma log_tendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma tendsto_defectRatio (v C : ℕ) :
    Tendsto (fun n : ℕ ↦ (traceCodeBase (sharpOffset n) v : ℝ)^C * (n : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
  let K : ℝ := 4*(v+2)+1
  have hLimit := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*C : ℝ) (1/2)
    (by norm_num)).comp log_tendsto
  have hBound : Tendsto (fun n : ℕ ↦ K^C * (Real.log (n : ℝ))^(2*C : ℝ) *
      Real.exp (-(1/2 : ℝ)*Real.log (n : ℝ))) atTop (𝓝 0) := by
    convert hLimit.const_mul (K^C) using 1
    · ext n
      simp only [Function.comp_apply]
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
    (Eventually.of_forall fun n ↦ by positivity) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ),log_tendsto.eventually_ge_atTop 1] with n hn hLog
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hCeil : (1 : ℕ) ≤ ⌈(Real.log (n : ℝ))^2⌉₊ :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hK : (sharpPowerHalf n : ℝ) ≤ 2*(Real.log (n : ℝ))^2 := by
    unfold sharpPowerHalf
    rw [max_eq_right hCeil]
    have he := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
    nlinarith
  have hB : (traceCodeBase (sharpOffset n) v : ℝ) ≤ K*(Real.log (n : ℝ))^2 := by
    unfold traceCodeBase
    rw [sharpOffset_add_two]
    push_cast
    unfold K
    have h := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ (v : ℝ)+2)
    nlinarith only [h,show (1 : ℝ) ≤ (Real.log (n : ℝ))^2 by nlinarith]
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hB C)
    (Real.rpow_nonneg hnR.le _))
  rw [Real.rpow_def_of_pos hnR,mul_pow,← pow_mul,mul_comm (Real.log (n : ℝ)) (-(1/2 : ℝ))]
  rw [show (2*C : ℝ) = ((2*C : ℕ) : ℝ) by push_cast; rfl,Real.rpow_natCast]

private lemma eventually_defectRatio_le (v C : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (traceCodeBase (sharpOffset n) v : ℝ)^C * (n : ℝ)^(-(1/2 : ℝ)) ≤ 1/2 :=
  (tendsto_defectRatio v C).eventually_le_const (by norm_num)

private lemma eventually_markov_ratio {ε m : ℝ} (hε : 0 < ε) (_hm : 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop, 2*(n : ℝ)*(2/(2+ε))^(2*sharpPowerHalf n) ≤ 2*(n : ℝ)^(-m-1) := by
  let ρ : ℝ := 2/(2+ε)
  have hρ₀ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ₁ : ρ < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let d := -Real.log ρ
  have hd : 0 < d := neg_pos.mpr (Real.log_neg hρ₀ hρ₁)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    log_tendsto.eventually_ge_atTop ((m+2)/(2*d))] with n hn hLog
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hLog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hCeil : ⌈(Real.log (n : ℝ))^(2 : ℕ)⌉₊ ≤ sharpPowerHalf n := le_max_right _ _
  have hK : (Real.log (n : ℝ))^2 ≤ (sharpPowerHalf n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hCeil)
  have hExp : (2/(2+ε))^(2*sharpPowerHalf n) ≤ (n : ℝ)^(-m-2) := by
    change ρ^_ ≤ _
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hρ₀,Real.rpow_def_of_pos hnR,Real.exp_le_exp]
    have h := (div_le_iff₀ (by positivity : 0 < 2*d)).mp hLog
    have h₁ := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ 2*d)
    have h₂ := mul_le_mul_of_nonneg_right h hLog₀
    push_cast
    rw [show Real.log ρ = -d from (neg_neg _).symm]
    nlinarith only [h₁,h₂]
  refine (mul_le_mul_of_nonneg_left hExp (by positivity)).trans_eq ?_
  calc
    _ = 2*((n : ℝ)^(1 : ℝ)*(n : ℝ)^(-m-2)) := by rw [Real.rpow_one,mul_assoc]
    _ = _ := by rw [← Real.rpow_add hnR]; congr 2; ring

variable {J : Type*} [Fintype J]

/-- At the logarithmic moment choice the geometric correction tends to one. -/
theorem eventually_average_trace_normalizedCombination_le (α : J → BasicShape)
    (hα : Function.Injective α) {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let L := 2*⌈(Real.log (n : ℝ))^2⌉₊
      average (fun x ↦ (normalizedCombination α c (n := n) x ^ L).trace) ≤
        (1+ε)*(n : ℝ)*2^L := by
  let v := (univ : Finset J).sup fun j ↦ (α j).additionalVertices
  let C := traceCodeExponent v (Fintype.card J)
  let q (n : ℕ) := (traceCodeBase (sharpOffset n) v : ℝ)^C * (n : ℝ)^(-(1/2 : ℝ))
  have hv (j : J) : (α j).additionalVertices ≤ v :=
    le_sup (f := fun j ↦ (α j).additionalVertices) (mem_univ j)
  have hQ : Tendsto q atTop (𝓝 0) := tendsto_defectRatio v C
  have hOne : Tendsto (fun n ↦ (1-q n)⁻¹) atTop (𝓝 1) := by
    have h : Tendsto (fun n ↦ 1-q n) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hQ
    simpa only [inv_one] using h.inv₀ one_ne_zero
  filter_upwards [hOne.eventually_le_const (by linarith : (1 : ℝ) < 1+ε),
    eventually_defectRatio_le v C,eventually_ge_atTop (1 : ℕ),log_tendsto.eventually_ge_atTop 1]
    with n hM hQ' hn hLog
  have hL : sharpOffset n+2 = 2*⌈(Real.log (n : ℝ))^2⌉₊ := by
    rw [sharpOffset_add_two,sharpPowerHalf,max_eq_right (Nat.one_le_ceil_iff.mpr (by positivity))]
  have hTrace := average_trace_normalizedCombination_le_geom (by omega : 0 < n) hα hv hc hQ'
  change _ ≤ (n : ℝ)*2^(sharpOffset n+2)/(1-q n) at hTrace
  rw [hL] at hTrace
  apply hTrace.trans
  rw [div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hM (by positivity)).trans_eq (by ring)

private lemma normalizedCombination_smul (α : J → BasicShape) (b : J → ℝ)
    (r : ℝ) {n : ℕ} (x : EdgeIndex (Fin n) → Bool) :
    normalizedCombination α (fun j ↦ r * b j) x = r • normalizedCombination α b x := by
  simp only [normalizedCombination,basicCombination,smul_sum,← mul_smul,mul_assoc]

private lemma normalizedCombination_zero (α : J → BasicShape) {n : ℕ} (x : EdgeIndex (Fin n) → Bool) :
    normalizedCombination α (fun _ ↦ 0) x = 0 := by
  simp [normalizedCombination,basicCombination]

private theorem eventually_probability_unit (α : J → BasicShape) (hα : Function.Injective α)
    (c : J → ℝ) (hc : ∑ j, (c j)^2 = 1)
    (hSym : ∀ n x, (normalizedCombination α c (n := n) x).IsSymm)
    {ε m : ℝ} (hε : 0 < ε) (hm : 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop, probability (fun x : EdgeIndex (Fin n) → Bool ↦
      2+ε < ‖normalizedCombination α c x‖) ≤ 2*(n : ℝ)^(-m-1) := by
  let v := (univ : Finset J).sup fun j ↦ (α j).additionalVertices
  have hv (j : J) : (α j).additionalVertices ≤ v := le_sup (f := fun j ↦ (α j).additionalVertices) (mem_univ j)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_defectRatio_le v (traceCodeExponent v (Fintype.card J)),
    eventually_markov_ratio hε hm] with n hn hRatio hMarkov
  have hn' : 0 < n := by omega
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  let T : ℝ := 2+ε
  have hT : 0 < T := by dsimp [T]; positivity
  let k := sharpPowerHalf n
  let M (x : EdgeIndex (Fin n) → Bool) := normalizedCombination α c x
  have hMoment := average_trace_normalizedCombination_le hn' hα hv hc hRatio
  rw [sharpOffset_add_two] at hMoment
  have hNormMoment : (average fun x ↦ ‖M x‖^(2*k)) ≤ 2*(n : ℝ)*2^(2*k) := by
    apply le_trans (average_mono ?_) hMoment
    intro x
    have hM := opNorm_pow_le_trace (M x) k
    have hs : (M x)ᵀ = M x := hSym n x
    have hDec : (fun a b : Fin n ↦ Classical.propDecidable (a = b)) = instDecidableEqFin n :=
      Subsingleton.elim _ _
    rw [hDec] at hM
    rw [hs,← pow_two,← pow_mul] at hM
    exact hM
  calc
    _ ≤ probability (fun x : EdgeIndex (Fin n) → Bool ↦ T^(2*k) ≤ ‖M x‖^(2*k)) :=
      probability_mono (fun _ hx ↦ pow_le_pow_left₀ hT.le hx.le _)
    _ ≤ (average fun x ↦ ‖M x‖^(2*k))/T^(2*k) :=
      probability_le_average_div _ (pow_pos hT _) (fun _ ↦ by positivity)
    _ ≤ _ := by
      refine (div_le_div_of_nonneg_right hNormMoment (pow_nonneg hT.le _)).trans ?_
      rw [mul_div_assoc,← div_pow]
      exact hMarkov

/-- Polynomially small failure probability for the sharp estimate, with one
additional inverse power for the little-o conclusion. -/
theorem eventually_probability_opNorm_normalizedCombination (α : J → BasicShape)
    (hα : Function.Injective α) (c : J → ℝ)
    (hSym : ∀ n x, (normalizedCombination α c (n := n) x).IsSymm)
    {ε m : ℝ} (hε : 0 < ε) (hm : 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop, probability (fun x : EdgeIndex (Fin n) → Bool ↦
      (2+ε)*Real.sqrt (∑ j, (c j)^2) < ‖normalizedCombination α c x‖) ≤ 2*(n : ℝ)^(-m-1) := by
  let a := Real.sqrt (∑ j, (c j)^2)
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have haSq : a^2 = ∑ j, (c j)^2 := Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)
  by_cases ha : a = 0
  · have hc (j : J) : c j = 0 := by
      have h := single_le_sum (f := fun k ↦ (c k)^2) (fun _ _ ↦ sq_nonneg _) (mem_univ j)
      rw [← haSq,ha,zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
      nlinarith
    have hc₀ : c = fun _ ↦ 0 := funext hc
    apply Eventually.of_forall
    intro n
    simp only [hc₀,normalizedCombination_zero,norm_zero]
    have hEmpty : probability (fun _ : EdgeIndex (Fin n) → Bool ↦ (2+ε)*Real.sqrt (∑ _ : J, (0 : ℝ)^2) < 0) = 0 := by
      simp [probability,average]
    rw [hEmpty]
    positivity
  · have ha' : 0 < a := lt_of_le_of_ne ha₀ (Ne.symm ha)
    let b (j : J) := c j/a
    have hb : ∑ j, (b j)^2 = 1 := by
      simp only [b,div_pow,← sum_div,haSq]
      rw [← haSq,div_self (pow_ne_zero _ ha)]
    have hScaled : (fun j ↦ a*b j) = c := by
      funext j
      dsimp only [b]
      rw [← mul_div_assoc,mul_comm a, mul_div_cancel_right₀ _ ha]
    have hMatrix (n : ℕ) (x : EdgeIndex (Fin n) → Bool) :
        normalizedCombination α c x = a • normalizedCombination α b x := by
      rw [← normalizedCombination_smul,hScaled]
    have hSymB (n : ℕ) (x : EdgeIndex (Fin n) → Bool) :
        (normalizedCombination α b x).IsSymm := by
      have h : (normalizedCombination α c x)ᵀ = normalizedCombination α c x := hSym n x
      rw [hMatrix,transpose_smul] at h
      exact (smul_right_injective (Matrix (Fin n) (Fin n) ℝ) ha) h
    filter_upwards [eventually_probability_unit α hα b hb hSymB hε hm] with n hn
    apply le_trans (probability_mono ?_) hn
    intro x hx
    rw [hMatrix,norm_smul,Real.norm_of_nonneg ha₀,mul_comm (2+ε)] at hx
    exact (mul_lt_mul_iff_right₀ ha').mp hx

end LovaszTheta.Independent
