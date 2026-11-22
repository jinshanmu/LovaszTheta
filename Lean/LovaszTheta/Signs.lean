module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Tactic

/-!
# Fair signs on a finite cube

Both random graph models use the uniform law on functions from a finite set
of sign indices to the two-element set. This file records the finite
expectation, orthogonality, sign flips, and the concentration bound used
for real linear combinations of these signs.
-/

@[expose] public section

open Finset
open scoped symmDiff

namespace LovaszTheta

/-- Expectation under the uniform law on a finite type. -/
noncomputable def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

lemma average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  unfold average
  exact div_le_div_of_nonneg_right (sum_le_sum fun x _ ↦ h x) (by positivity)

lemma average_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f :=
  div_nonneg (sum_nonneg fun x _ ↦ h x) (by positivity)

@[simp]
lemma average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω ↦ c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, h]

lemma average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, sum_add_distrib, add_div]

lemma average_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, sum_sub_distrib, sub_div]

lemma average_mul_left {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    average (fun x ↦ c * f x) = c * average f := by
  rw [average, average, ← mul_sum, mul_div_assoc]

lemma average_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (f : Ω' → ℝ) :
    average (fun x ↦ f (e x)) = average f := by
  unfold average
  rw [← Fintype.card_congr e, ← Equiv.sum_comp e f]

lemma average_finsetSum {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (f : ι → Ω → ℝ) :
    average (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

lemma average_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    average (fun x ↦ ∑ i, f i x) = ∑ i, average (f i) :=
  average_finsetSum univ f

/-- The probability of an event under the uniform law. -/
noncomputable def probability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℝ := by
  classical
  exact average fun x ↦ if p x then 1 else 0

lemma probability_mono {Ω : Type*} [Fintype Ω] {p q : Ω → Prop}
    (h : ∀ x, p x → q x) : probability p ≤ probability q := by
  classical
  unfold probability
  apply average_mono
  intro x
  by_cases hx : p x
  · simp [hx, h x hx]
  · by_cases hq : q x <;> simp [hx, hq]

lemma probability_le_add {Ω : Type*} [Fintype Ω] (p q : Ω → Prop) :
    probability (fun x ↦ p x ∨ q x) ≤ probability p + probability q := by
  classical
  unfold probability
  rw [← average_add]
  apply average_mono
  intro x
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

/-- The finite union bound under the uniform law. -/
lemma probability_exists_le_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : ι → Ω → Prop) :
    probability (fun x ↦ ∃ i, p i x) ≤ ∑ i, probability (p i) := by
  classical
  unfold probability
  rw [← average_sum]
  apply average_mono
  intro x
  have hNonneg (i : ι) : 0 ≤ (if p i x then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h : ∃ i, p i x
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      (1 : ℝ) = (if p i x then 1 else 0) := by simp [hi]
      _ ≤ _ := Finset.single_le_sum (fun j _ ↦ hNonneg j) (mem_univ i)
  · rw [ite_eq_right h]
    exact sum_nonneg fun i _ ↦ hNonneg i

/-- Markov's inequality under the uniform law. -/
lemma probability_le_average_div {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) {t : ℝ}
    (ht : 0 < t) (hf : ∀ x, 0 ≤ f x) :
    probability (fun x ↦ t ≤ f x) ≤ average f / t := by
  classical
  rw [le_div_iff₀ ht, mul_comm]
  change t * average (fun x ↦ if t ≤ f x then 1 else 0) ≤ average f
  rw [← average_mul_left]
  apply average_mono
  intro x
  by_cases hx : t ≤ f x
  · simp [hx]
  · simpa [hx] using hf x

/-- A Boolean coordinate with the numerical values (-1) and (1). -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sign_true : sign true = 1 := rfl
@[simp] lemma sign_false : sign false = -1 := rfl
@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num
@[simp] lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num
@[simp] lemma abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num

/-- The character indexed by a subset of the sign coordinates. -/
def walsh {ι : Type*} (s : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ s, sign (x i)

/-- The involution that changes the sign at one specified index. -/
def flip {ι : Type*} [DecidableEq ι] (i : ι) : (ι → Bool) ≃ (ι → Bool) :=
  (show Function.Involutive (fun (x : ι → Bool) j ↦ if j = i then !(x j) else x j) by
    intro x
    funext j
    by_cases h : j = i <;> simp [h]).toPerm

lemma flip_same {ι : Type*} [DecidableEq ι] (i : ι) (x : ι → Bool) :
    flip i x i = !(x i) := by simp [flip, Function.Involutive.toPerm]

lemma flip_other {ι : Type*} [DecidableEq ι] {i j : ι} (h : j ≠ i) (x : ι → Bool) :
    flip i x j = x j := by simp [flip, Function.Involutive.toPerm, h]

lemma walsh_flip {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (x : ι → Bool) :
    walsh s (flip i x) = if i ∈ s then -walsh s x else walsh s x := by
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, walsh, walsh, prod_eq_mul_prod_sdiff_singleton_of_mem hi,
      prod_eq_mul_prod_sdiff_singleton_of_mem hi, flip_same, sign_not, neg_mul]
    exact congrArg (fun y ↦ -(sign (x i) * y))
      (prod_congr rfl fun j hj ↦ by rw [flip_other (by simpa using (mem_sdiff.mp hj).2)])
  · rw [ite_eq_right hi]
    apply prod_congr rfl
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hi hj
    rw [flip_other hji]

@[simp]
lemma walsh_sq {ι : Type*} (s : Finset ι) (x : ι → Bool) : walsh s x ^ 2 = 1 := by
  rw [walsh, ← prod_pow]; exact prod_eq_one fun i _ ↦ sign_sq (x i)

/-- Orthogonality of distinct Walsh characters on the fair-sign cube. -/
theorem average_walsh_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (s t : Finset ι) :
    average (fun x ↦ walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  by_cases h : s = t
  · subst t
    simp [← pow_two]
  · rw [ite_eq_right h]
    have hcancel (a b : Finset ι) (i : ι) (ha : i ∈ a) (hb : i ∉ b) :
        average (fun x ↦ walsh a x * walsh b x) = 0 := by
      have hAvg := average_equiv (flip i) (fun x ↦ walsh a x * walsh b x)
      simp only [walsh_flip, ite_eq_left ha, ite_eq_right hb, neg_mul] at hAvg
      have h' : -average (fun x ↦ walsh a x * walsh b x) =
          average (fun x ↦ walsh a x * walsh b x) := by
        rw [← neg_one_mul (average _), ← average_mul_left]
        simpa only [neg_one_mul] using hAvg
      linarith
    by_cases hst : s ⊆ t
    · obtain ⟨i, hi, his⟩ := not_subset.mp fun hts ↦ h (Subset.antisymm hst hts)
      simpa only [mul_comm] using hcancel t s i hi his
    · obtain ⟨i, hi, hit⟩ := not_subset.mp hst
      exact hcancel s t i hi hit

/-- A linear combination of Walsh characters. -/
noncomputable def walshCombination {ι : Type*} [Fintype ι]
    (c : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ s : Finset ι, c s * walsh s x

/-- Taking the expectation of two Walsh combinations gives their coefficient pairing. -/
lemma average_walshCombination_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : Finset ι → ℝ) :
    average (fun x ↦ walshCombination c x * walshCombination d x) = ∑ s, c s * d s := by
  classical
  have hTerms (x : ι → Bool) :
      walshCombination c x * walshCombination d x =
        ∑ s : Finset ι, ∑ t : Finset ι, (c s * walsh s x) * (d t * walsh t x) := by
    unfold walshCombination
    rw [sum_mul]
    exact sum_congr rfl fun _ _ ↦ mul_sum _ _ _
  simp_rw [hTerms, average_sum]
  apply sum_congr rfl
  intro s _
  have h (t : Finset ι) :
      average (fun x ↦ c s * walsh s x * (d t * walsh t x)) =
        if s = t then c s * d t else 0 := by
    have hProd (x : ι → Bool) :
        c s * walsh s x * (d t * walsh t x) = (c s * d t) * (walsh s x * walsh t x) := by ring
    simp_rw [hProd, average_mul_left, average_walsh_mul]
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq, ite_eq_left (mem_univ s)]

/-- A product of single-coordinate tests factors under a uniform product law. -/
lemma average_product {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] (g : ι → β → ℝ) :
    average (fun (x : ι → β) ↦ ∏ i, g i (x i)) = ∏ i, average (g i) := by
  classical
  simp only [average, Fintype.card_fun, Nat.cast_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]
  congr 1
  simpa only [Fintype.piFinset_univ] using sum_prod_piFinset (univ : Finset β) g

/-- Multiplying Walsh characters cancels repeated sign indices. -/
lemma walsh_mul {ι : Type*} [DecidableEq ι] (s t : Finset ι) (x : ι → Bool) :
    walsh s x * walsh t x = walsh (s ∆ t) x := by
  change (∏ i ∈ s, sign (x i)) * (∏ i ∈ t, sign (x i)) =
    ∏ i ∈ s ∆ t, sign (x i)
  let f : ι → ℝ := fun i ↦ sign (x i)
  change (∏ i ∈ s, f i) * (∏ i ∈ t, f i) = ∏ i ∈ s ∆ t, f i
  rw [← prod_inter_mul_prod_sdiff s t f, ← prod_inter_mul_prod_sdiff t s f, inter_comm t s]
  have hSq : (∏ i ∈ s ∩ t, f i) ^ 2 = 1 := walsh_sq (s ∩ t) x
  rw [Finset.symmDiff_def, Finset.prod_union]
  · calc
      _ = (∏ i ∈ s ∩ t, f i) ^ 2 * ((∏ i ∈ s \ t, f i) * ∏ i ∈ t \ s, f i) := by ring
      _ = _ := by rw [hSq, one_mul]
  · exact disjoint_left.mpr fun i hi hj ↦ (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1

lemma average_walsh {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) :
    average (walsh s) = if s = ∅ then 1 else 0 := by
  change average (fun (x : ι → Bool) ↦ ∏ i ∈ s, sign (x i)) = _
  simpa [walsh] using average_walsh_mul s (∅ : Finset ι)

private lemma average_exp_signSum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (s : ℝ) :
    average (fun (x : ι → Bool) ↦ Real.exp (s * ∑ i, a i * sign (x i))) ≤
      Real.exp (s ^ 2 * (∑ i, a i ^ 2) / 2) := by
  have hExp (x : ι → Bool) : Real.exp (s * ∑ i, a i * sign (x i)) =
      ∏ i, Real.exp (s * (a i * sign (x i))) := by
    rw [mul_sum, Real.exp_sum]
  have hPow : s ^ 2 * (∑ i, a i ^ 2) / 2 = ∑ i, (s * a i) ^ 2 / 2 := by
    simp only [mul_sum, sum_div, mul_pow]
  simp_rw [hExp]
  rw [average_product (fun i b ↦ Real.exp (s * (a i * sign b))), hPow, Real.exp_sum]
  apply prod_le_prod₀
  · intro i _
    unfold average
    positivity
  · intro i _
    have h : average (fun b ↦ Real.exp (s * (a i * sign b))) = Real.cosh (s * a i) := by
      rw [Real.cosh_eq]
      simp [average, ← mul_assoc]
    rw [h]
    exact Real.cosh_le_exp_half_sq _

/-- Hoeffding's two-sided bound for a real sum of independent fair signs. -/
theorem probability_abs_signSum_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) {t B : ℝ}
    (ht : 0 < t) (hB : 0 < B) (ha : ∑ i, a i ^ 2 ≤ B) :
    probability (fun (x : ι → Bool) ↦ t ≤ |∑ i, a i * sign (x i)|) ≤ 2 * Real.exp (-(t ^ 2) / (2 * B)) := by
  classical
  have upper (c : ι → ℝ) (hc : ∑ i, c i ^ 2 ≤ B) :
      probability (fun (x : ι → Bool) ↦ t ≤ ∑ i, c i * sign (x i)) ≤ Real.exp (-(t ^ 2) / (2 * B)) := by
    let s := t / B
    have hs : 0 < s := div_pos ht hB
    have hexp (x : ι → Bool) :
        t ≤ ∑ i, c i * sign (x i) ↔
        Real.exp (s * t) ≤ Real.exp (s * ∑ i, c i * sign (x i)) := by
      rw [Real.exp_le_exp, mul_le_mul_iff_right₀ hs]
    simp_rw [hexp]
    calc
      _ ≤ average (fun (x : ι → Bool) ↦ Real.exp (s * ∑ i, c i * sign (x i))) / Real.exp (s * t) :=
        probability_le_average_div _ (Real.exp_pos _) fun _ ↦ (Real.exp_pos _).le
      _ ≤ Real.exp (s ^ 2 * (∑ i, c i ^ 2) / 2) / Real.exp (s * t) :=
        div_le_div_of_nonneg_right (average_exp_signSum c s) (Real.exp_pos (s * t)).le
      _ ≤ Real.exp (-(t ^ 2) / (2 * B)) := by
        rw [← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ s ^ 2 * B / 2 - s * t :=
            sub_le_sub_right (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc (sq_nonneg s)) (by norm_num)) _
          _ = -(t ^ 2) / (2 * B) := by dsimp [s]; field_simp; ring
  have hneg := upper (fun i ↦ -a i) (by simpa using ha)
  simp only [neg_mul, sum_neg_distrib] at hneg
  have h := probability_le_add (fun (x : ι → Bool) ↦ t ≤ ∑ i, a i * sign (x i))
    (fun x ↦ t ≤ -(∑ i, a i * sign (x i)))
  have hEvent (x : ι → Bool) : t ≤ |∑ i, a i * sign (x i)| ↔
      t ≤ (∑ i, a i * sign (x i)) ∨ t ≤ -(∑ i, a i * sign (x i)) := by
    rw [abs_eq_max_neg, le_max_iff]
  simp_rw [hEvent]
  exact h.trans (by linarith [upper a ha])

end LovaszTheta
