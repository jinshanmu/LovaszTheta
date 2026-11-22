module

public import LovaszTheta.TwoPointMoment
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Option

/-!
# Hypercontractivity on the sign cube

Separate the terms that contain a chosen sign from the terms that
omit it. The two-point inequality and the triangle inequality in
the half-order moment propagate a factor of (2m-1) on the squared
coefficient of each term that contains that sign.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

private noncomputable def absMomentRoot {Ω : Type*} [Fintype Ω] (m : ℕ) (f : Ω → ℝ) : ℝ :=
  (average fun x ↦ |f x| ^ m) ^ (1 / (m : ℝ))

private lemma average_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f :=
  div_nonneg (sum_nonneg fun x _ ↦ h x) (by positivity)

private lemma absMomentRoot_add_le {Ω : Type*} [Fintype Ω] {m : ℕ} (hm : 0 < m)
    (f g : Ω → ℝ) :
    absMomentRoot m (fun x ↦ f x + g x) ≤ absMomentRoot m f + absMomentRoot m g := by
  have hOrder : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Real.Lp_add_le univ f g hOrder
  simp only [Real.rpow_natCast] at h
  have hScale (u : Ω → ℝ) :
      absMomentRoot m u = (∑ i, |u i| ^ m) ^ (1 / (m : ℝ)) *
        ((Fintype.card Ω : ℝ)⁻¹) ^ (1 / (m : ℝ)) := by
    rw [absMomentRoot, average, div_eq_mul_inv,
      Real.mul_rpow (sum_nonneg fun _ _ ↦ pow_nonneg (abs_nonneg _) _) (by positivity)]
  rw [hScale, hScale, hScale, ← add_mul]
  exact mul_le_mul_of_nonneg_right h (by positivity)

private lemma absMomentRoot_const_mul {Ω : Type*} [Fintype Ω] {m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 0 ≤ c) (f : Ω → ℝ) :
    absMomentRoot m (fun x ↦ c * f x) = c * absMomentRoot m f := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hPow : (c ^ m) ^ (1 / (m : ℝ)) = c := by
    rw [← Real.rpow_natCast_mul hc, mul_one_div_cancel hmR, Real.rpow_one]
  unfold absMomentRoot
  simp_rw [abs_mul, abs_of_nonneg hc, mul_pow]
  rw [average_mul_left, Real.mul_rpow (pow_nonneg hc _) (average_nonneg fun _ ↦ by positivity), hPow]

private lemma absMomentRoot_sq {Ω : Type*} [Fintype Ω] (m : ℕ) (f : Ω → ℝ) :
    absMomentRoot m (fun x ↦ f x ^ 2) = (average fun x ↦ f x ^ (2*m)) ^ (1 / (m : ℝ)) := by
  unfold absMomentRoot
  have h (x : Ω) : |f x ^ 2| = f x ^ 2 := abs_of_nonneg (sq_nonneg _)
  simp_rw [h, pow_mul]

private noncomputable def optionFinsetsEquiv (I : Type*) : Bool × Finset I ≃ Finset (Option I) where
  toFun p := if p.1 then p.2.insertNone else p.2.map Function.Embedding.some
  invFun s := (decide (none ∈ s), s.eraseNone)
  left_inv := by
    rintro ⟨b, s⟩
    cases b <;> simp
  right_inv := by
    intro s
    by_cases h : none ∈ s
    · simp [h, insertNone_eraseNone, insert_eq_of_mem h]
    · simp [h, map_some_eraseNone]

private lemma walsh_some {I : Type*} (s : Finset I) (x : Option I → Bool) :
    walsh (s.map Function.Embedding.some) x = walsh s (fun i ↦ x (some i)) := by
  rw [walsh, prod_map, walsh]
  rfl

private lemma walsh_insertNone {I : Type*} (s : Finset I) (x : Option I → Bool) :
    walsh s.insertNone x = sign (x none) * walsh s (fun i ↦ x (some i)) := by
  rw [walsh, show (s.insertNone : Finset (Option I)) =
    insert none (s.map Function.Embedding.some) by ext (_ | i) <;> simp,
    prod_insert (by simp), ← walsh, walsh_some]

private lemma walshCombination_option {I : Type*} [Fintype I]
    (c : Finset (Option I) → ℝ) (x : Option I → Bool) :
    walshCombination c x =
      walshCombination (fun s ↦ c (s.map Function.Embedding.some)) (fun i ↦ x (some i)) +
        sign (x none) * walshCombination (fun s ↦ c s.insertNone) (fun i ↦ x (some i)) := by
  unfold walshCombination
  rw [← Equiv.sum_comp (optionFinsetsEquiv I)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, optionFinsetsEquiv, Equiv.coe_fn_mk,
    Bool.false_eq_true, ite_false, ite_true, walsh_some, walsh_insertNone, mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun _ _ ↦ by ring

private lemma average_option_signs {I : Type*} [Fintype I] (f : (Option I → Bool) → ℝ) :
    average f = average (fun x : I → Bool ↦
      (f (fun a ↦ a.elim true x) + f (fun a ↦ a.elim false x)) / 2) := by
  rw [← average_equiv (Equiv.piOptionEquivProd (β := fun _ : Option I ↦ Bool)).symm f]
  unfold average
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool]
  rw [sum_comm]
  simp only [Fintype.sum_bool, Nat.cast_mul, Nat.cast_ofNat, ← sum_div, div_div]
  have h (b : Bool) (x : I → Bool) :
      (Equiv.piOptionEquivProd (β := fun _ : Option I ↦ Bool)).symm (b, x) =
        fun a ↦ a.elim b x := by
    funext a
    cases a <;> rfl
  simp_rw [h]

private noncomputable def weightedCoefficients {I : Type*} [Fintype I]
    (m : ℕ) (c : Finset I → ℝ) : ℝ :=
  ∑ s : Finset I, ((2*m-1 : ℕ) : ℝ) ^ s.card * c s ^ 2

private lemma weightedCoefficients_option {I : Type*} [Fintype I]
    (m : ℕ) (c : Finset (Option I) → ℝ) :
    weightedCoefficients m c =
      weightedCoefficients m (fun s ↦ c (s.map Function.Embedding.some)) +
        ((2*m-1 : ℕ) : ℝ) * weightedCoefficients m (fun s ↦ c s.insertNone) := by
  unfold weightedCoefficients
  rw [← Equiv.sum_comp (optionFinsetsEquiv I)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, optionFinsetsEquiv, Equiv.coe_fn_mk,
    Bool.false_eq_true, ite_false, ite_true, card_map, card_insertNone, pow_succ, mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun _ _ ↦ by ring

private lemma moment_option_le {I : Type*} [Fintype I]
    {m : ℕ} (hm : 0 < m) (c : Finset (Option I) → ℝ) (finiteCube : Fintype (Option I → Bool)) :
    @absMomentRoot _ finiteCube m (fun x ↦ walshCombination c x ^ 2) ≤
      absMomentRoot m (fun x ↦ walshCombination (fun s ↦ c (s.map Function.Embedding.some)) x ^ 2) +
        ((2*m-1 : ℕ) : ℝ) *
          absMomentRoot m (fun x ↦ walshCombination (fun s ↦ c s.insertNone) x ^ 2) := by
  let cube := @Pi.instFintype (Option I) (fun _ ↦ Bool) inferInstance inferInstance
    (fun _ ↦ inferInstance)
  rw [show finiteCube = cube from Subsingleton.elim _ _]
  clear finiteCube
  let q := ((2*m-1 : ℕ) : ℝ)
  have hq : 0 ≤ q := by positivity
  let f (x : I → Bool) := walshCombination (fun s ↦ c (s.map Function.Embedding.some)) x
  let g (x : I → Bool) := walshCombination (fun s ↦ c s.insertNone) x
  have hPoint : (average fun x ↦ walshCombination c x ^ (2*m)) ≤
      average (fun x ↦ (f x ^ 2 + q * g x ^ 2) ^ m) := by
    rw [average_option_signs]
    apply average_mono
    intro x
    simp only [walshCombination_option, Option.elim_some, Option.elim_none, sign_true,
      sign_false, one_mul, neg_one_mul, ← sub_eq_add_neg]
    exact twoPoint_even_moment_le (f x) (g x) m
  calc
    _ ≤ absMomentRoot m (fun x ↦ f x ^ 2 + q * g x ^ 2) := by
      rw [absMomentRoot_sq]
      unfold absMomentRoot
      simp only [abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hq (sq_nonneg _)))]
      have hAvg : 0 ≤ average (fun x ↦ walshCombination c x ^ (2*m)) :=
        average_nonneg fun x ↦ by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
      exact Real.rpow_le_rpow hAvg hPoint (by positivity)
    _ ≤ absMomentRoot m (fun x ↦ f x ^ 2) + q * absMomentRoot m (fun x ↦ g x ^ 2) := by
      rw [← absMomentRoot_const_mul hm hq]
      exact absMomentRoot_add_le hm _ _

private lemma walshCombination_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (c : Finset J → ℝ) (x : J → Bool) :
    walshCombination c x = walshCombination (fun s ↦ c (e.finsetCongr s)) (x ∘ e) := by
  unfold walshCombination
  rw [← Equiv.sum_comp e.finsetCongr (fun s ↦ c s * walsh s x)]
  simp only [Equiv.finsetCongr_apply, walsh, prod_map, Equiv.toEmbedding_apply, Function.comp_apply]

universe u

private lemma absMomentRoot_walsh_le {I : Type u} [Fintype I]
    {m : ℕ} (hm : 0 < m) (c : Finset I → ℝ) :
    absMomentRoot m (fun x ↦ walshCombination c x ^ 2) ≤ weightedCoefficients m c := by
  revert c
  refine Fintype.induction_empty_option (P := fun I _ ↦ ∀ c : Finset I → ℝ,
    absMomentRoot m (fun x ↦ walshCombination c x ^ 2) ≤ weightedCoefficients m c) ?_ ?_ ?_ I
  · intro I J instJ e ih c
    let : Fintype I := Fintype.ofEquiv J e.symm
    let eSigns := e.arrowCongr (Equiv.refl Bool)
    let d (s : Finset I) := c (e.finsetCongr s)
    have hEq (x : I → Bool) : walshCombination c (eSigns x) = walshCombination d x := by
      rw [walshCombination_equiv e c]
      congr 1
      funext a
      simp [eSigns]
    have hw : weightedCoefficients m c = weightedCoefficients m d := by
      unfold weightedCoefficients
      rw [← Equiv.sum_comp e.finsetCongr]
      simp [d]
    unfold absMomentRoot
    rw [← average_equiv eSigns, hw]
    simp_rw [hEq]
    exact ih d
  · intro c
    rw [absMomentRoot_sq]
    have hEmpty : (default : Finset (PEmpty : Type u)) = ∅ := Subsingleton.elim _ _
    simp only [walshCombination, walsh, weightedCoefficients, univ_unique, sum_singleton,
      hEmpty, prod_empty, mul_one, card_empty, pow_zero, one_mul, average_const]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [pow_mul, ← Real.rpow_natCast_mul (sq_nonneg _), mul_one_div_cancel hmR, Real.rpow_one]
  · intro I instI ih c
    refine (moment_option_le hm c _).trans ?_
    rw [weightedCoefficients_option]
    exact add_le_add (ih _) (mul_le_mul_of_nonneg_left (ih _) (by positivity))

/-- The even-moment form of the manuscript's hypercontractive inequality
for a Walsh polynomial of degree at most D. -/
theorem average_even_pow_walshCombination_le {I : Type*} [Fintype I] {m : ℕ} (hm : 0 < m)
    (c : Finset I → ℝ) (D : ℕ) (hDegree : ∀ s, D < s.card → c s = 0) :
    average (fun x ↦ walshCombination c x ^ (2*m)) ≤
      (((2*m-1 : ℕ) : ℝ)^D * average (fun x ↦ walshCombination c x ^ 2)) ^ m := by
  let q := ((2*m-1 : ℕ) : ℝ)
  have hq : 1 ≤ q := by
    change (1 : ℝ) ≤ ((2*m-1 : ℕ) : ℝ)
    have h : 1 ≤ 2*m-1 := by omega
    exact_mod_cast h
  have hW : weightedCoefficients m c ≤ q^D * (∑ s, c s ^ 2) := by
    unfold weightedCoefficients
    rw [mul_sum]
    apply sum_le_sum
    intro s _
    by_cases h : s.card ≤ D
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq h) (sq_nonneg _)
    · simp [hDegree s (lt_of_not_ge h)]
  have hRoot := (absMomentRoot_walsh_le hm c).trans hW
  rw [absMomentRoot_sq] at hRoot
  have hSq : (∑ s, c s ^ 2) = average (fun x ↦ walshCombination c x ^ 2) := by
    simpa only [pow_two] using (average_walshCombination_mul c c).symm
  rw [hSq] at hRoot
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAvg : 0 ≤ average (fun x ↦ walshCombination c x ^ (2*m)) :=
    average_nonneg fun x ↦ by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  have hPow := pow_le_pow_left₀ (Real.rpow_nonneg hAvg _) hRoot m
  rwa [← Real.rpow_mul_natCast hAvg, one_div_mul_cancel hmR, Real.rpow_one] at hPow

end LovaszTheta.Circulant
