module

public import LovaszTheta.RoughNorm

/-!
# Operator-norm errors

Finite families of error events can be combined at any fixed inverse
power of the vertex count. A graph matrix with a strictly negative
net normalization power has a vanishing operator-norm contribution.
-/

@[expose] public section

open Filter Finset
open scoped Classical Topology Matrix.Norms.L2Operator

namespace LovaszTheta.Independent

/-- A realization of the independent edge signs. -/
abbrev SignSample (n : ℕ) := EdgeIndex (Fin n) → Bool

/-- A square matrix depending on the order and its edge signs. -/
abbrev MatrixFamily := (n : ℕ) → SignSample n → Matrix (Fin n) (Fin n) ℝ

/-- For every fixed inverse power, the failure probability is eventually bounded by that power. -/
def WithHighProbability (p : (n : ℕ) → SignSample n → Prop) : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ᶠ n : ℕ in atTop, probability (fun x : SignSample n ↦ ¬p n x) ≤ (n : ℝ)^(-m)

namespace WithHighProbability

variable {p q : (n : ℕ) → SignSample n → Prop}

lemma mono (hp : WithHighProbability p) (hpq : ∀ n x, p n x → q n x) : WithHighProbability q := by
  intro m hm
  filter_upwards [hp m hm] with n hn
  exact (probability_mono (fun x hq' hp' ↦ hq' (hpq n x hp'))).trans hn

lemma of_eventually (h : ∀ᶠ n : ℕ in atTop, ∀ x, p n x) : WithHighProbability p := by
  intro m hm
  filter_upwards [h] with n hn
  simp only [probability,hn,not_true_eq_false,ite_false,average,sum_const_zero,zero_div]
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma and (hp : WithHighProbability p) (hq : WithHighProbability q) :
    WithHighProbability (fun n x ↦ p n x ∧ q n x) := by
  intro m hm
  filter_upwards [hp (m+1) (by linarith),hq (m+1) (by linarith),eventually_ge_atTop (2 : ℕ)]
    with n h₁ h₂ hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  calc
    _ ≤ probability (fun x : SignSample n ↦ ¬p n x) + probability (fun x : SignSample n ↦ ¬q n x) :=
      (probability_mono fun _ h ↦ not_and_or.mp h).trans (probability_le_add _ _)
    _ ≤ (n : ℝ)^(-(m+1))+(n : ℝ)^(-(m+1)) := add_le_add h₁ h₂
    _ = ((n : ℝ)^(-m))*(2/(n : ℝ)) := by
      rw [neg_add,Real.rpow_add hpos,Real.rpow_neg_one]
      ring
    _ ≤ _ := mul_le_of_le_one_right (Real.rpow_nonneg hpos.le _) ((div_le_one hpos).mpr hn')

lemma forall_mem {ι : Type*} (s : Finset ι) (p : ι → (n : ℕ) → SignSample n → Prop)
    (h : ∀ i ∈ s, WithHighProbability (p i)) :
    WithHighProbability (fun n x ↦ ∀ i ∈ s, p i n x) := by
  induction s using Finset.induction_on with
  | empty =>
    exact of_eventually (Eventually.of_forall fun _ _ _ h ↦ (notMem_empty _ h).elim)
  | @insert i s hnot ih =>
    have hi := h i (mem_insert_self _ _)
    have hs := ih (fun j hj ↦ h j (mem_insert_of_mem hj))
    exact (hi.and hs).mono (fun _ _ he j hj ↦ (mem_insert.mp hj).elim (fun hj' ↦ hj'.symm ▸ he.1) (he.2 j))

end WithHighProbability

/-- Operator-norm convergence to zero with each fixed inverse-power failure bound. -/
def NormVanishes (A : MatrixFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → WithHighProbability (fun n x ↦ ‖A n x‖ ≤ ε)

namespace NormVanishes

variable {A B : MatrixFamily}

lemma of_zero : NormVanishes (fun _ _ ↦ 0) := fun _ h ↦
  WithHighProbability.of_eventually (Eventually.of_forall fun _ _ ↦ norm_zero.trans_le h.le)

lemma congr (h : NormVanishes A) (he : ∀ᶠ n : ℕ in atTop, ∀ x, A n x = B n x) : NormVanishes B := by
  intro ε hε
  exact ((h ε hε).and (WithHighProbability.of_eventually he)).mono
    (fun _ _ hh ↦ hh.2 ▸ hh.1)

lemma add (hA : NormVanishes A) (hB : NormVanishes B) :
    NormVanishes (fun n x ↦ A n x + B n x) := by
  intro ε hε
  have h : 0 < ε/2 := by positivity
  refine ((hA (ε/2) h).and (hB (ε/2) h)).mono ?_
  intro n x hx
  exact (norm_add_le _ _).trans (by linarith [hx.1,hx.2])

lemma smul (hA : NormVanishes A) (r : ℝ) :
    NormVanishes (fun n x ↦ r • A n x) := by
  intro ε hε
  have hA' := hA (ε/(|r|+1)) (by positivity)
  refine hA'.mono (fun n x hx ↦ ?_)
  rw [norm_smul,Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans ?_
  rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0 < |r|+1)]
  nlinarith

lemma neg (hA : NormVanishes A) : NormVanishes (fun n x ↦ -A n x) := by
  intro ε hε
  exact (hA ε hε).mono (fun _ _ h ↦ by rwa [norm_neg])

lemma sub (hA : NormVanishes A) (hB : NormVanishes B) :
    NormVanishes (fun n x ↦ A n x - B n x) :=
  (hA.add hB.neg).congr (Eventually.of_forall fun _ _ ↦ (sub_eq_add_neg _ _).symm)

lemma sum {ι : Type*} (s : Finset ι) (A : ι → MatrixFamily)
    (h : ∀ i ∈ s, NormVanishes (A i)) : NormVanishes (fun n x ↦ ∑ i ∈ s, A i n x) := by
  induction s using Finset.induction_on with
  | empty => exact of_zero.congr (Eventually.of_forall fun _ _ ↦ sum_empty.symm)
  | @insert i s hnot ih =>
    exact ((h i (mem_insert_self _ _)).add (ih fun j hj ↦ h j (mem_insert_of_mem hj))).congr
      (Eventually.of_forall fun n x ↦ (sum_insert (f := fun j ↦ A j n x) hnot).symm)

lemma mul_right (hA : NormVanishes A) {K : ℝ} (hK : 0 ≤ K)
    (hB : WithHighProbability (fun n x ↦ ‖B n x‖ ≤ K)) :
    NormVanishes (fun n x ↦ A n x * B n x) := by
  intro ε hε
  refine ((hA (ε/(K+1)) (by positivity)).and hB).mono (fun n x hx ↦ ?_)
  refine (norm_mul_le _ _).trans ((mul_le_mul hx.1 hx.2 (norm_nonneg _) (by positivity)).trans ?_)
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < K+1)]
  nlinarith

end NormVanishes

/-- The exponent in the unnormalized rough bound. -/
noncomputable def roughExponent (P : Shape) : ℝ :=
  ((P.vertexCount+P.isolatedInterior.card-P.boundaryIndicator : ℕ) : ℝ)/2

/-- A negative net power also absorbs the fixed logarithmic power in the rough estimate. -/
theorem normVanishes_smul_graphMatrix (P : Shape) (a : ℕ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : r+roughExponent P < 0)
    (ha : ∀ᶠ n : ℕ in atTop, |a n| ≤ C*(n : ℝ)^r) :
    NormVanishes (fun n x ↦ a n • graphMatrix P x) := by
  intro ε hε m hm
  let v := P.vertexCount
  let B := (4*(v : ℝ)^2)^v*Real.exp ((m+1)/2)
  let d := -(r+roughExponent P)
  have hd : 0 < d := neg_pos.mpr hr
  have hLim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (v : ℝ) d hd).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun n : ℕ ↦ (C*B)*(Real.log (n : ℝ))^v*Real.exp (-d*Real.log (n : ℝ))) atTop (𝓝 0) := by
    convert hLim.const_mul (C*B) using 1
    · ext n
      simp only [Function.comp_apply,Real.rpow_natCast]
      ring
    · simp
  filter_upwards [ha,eventually_ge_atTop (3 : ℕ),hl.eventually_le_const hε] with n hA hn hSmall
  have hPos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hRough := probability_opNorm_graphMatrix_gt (V := Fin n) P (by simpa using hn) hm
  have hDec : (fun a b : Fin n ↦ Classical.propDecidable (a = b)) = instDecidableEqFin n :=
    Subsingleton.elim _ _
  rw [Fintype.card_fin,hDec] at hRough
  apply le_trans (probability_mono ?_) hRough
  intro x hx
  by_contra! hGood
  have hGood' : ‖graphMatrix P x‖ ≤ B*Real.log (n : ℝ)^v*(n : ℝ)^(roughExponent P) := by
    unfold B v roughExponent
    convert hGood using 1
    ring
  apply hx
  rw [norm_smul,Real.norm_eq_abs]
  have hBound := mul_le_mul hA hGood' (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hPos.le _))
  refine hBound.trans ?_
  calc
    _ = (C*B)*Real.log (n : ℝ)^v*((n : ℝ)^r*(n : ℝ)^(roughExponent P)) := by ring
    _ = (C*B)*Real.log (n : ℝ)^v*Real.exp (-d*Real.log (n : ℝ)) := by
      rw [← Real.rpow_add hPos,Real.rpow_def_of_pos hPos]
      congr 2
      unfold d
      ring
    _ ≤ _ := hSmall

end LovaszTheta.Independent
