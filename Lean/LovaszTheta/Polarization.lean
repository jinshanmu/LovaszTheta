module

public import LovaszTheta.Signs
public import Mathlib.Data.Fintype.Perm

/-!
# Sign polarization of a monomial

Expanding the power gives a sum over functions on its positions.
A position omitted by the function leaves one unmatched sign.
The surviving functions are the permutations, each contributing
the original monomial.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

private lemma average_polarization_signs {d : ℕ} (f : Fin d → Fin d) :
    average (fun η ↦ walsh univ η * ∏ i, sign (η (f i))) =
      if Function.Bijective f then 1 else 0 := by
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    let e : Equiv.Perm (Fin d) := Equiv.ofBijective f hf
    have h (η : Fin d → Bool) : (∏ i, sign (η (f i))) = ∏ j, sign (η j) :=
      Equiv.prod_comp e (fun j ↦ sign (η j))
    simp_rw [h, walsh, ← prod_mul_distrib, ← pow_two, sign_sq, prod_const_one, average_const]
  · rw [ite_eq_right hf]
    have hns : ¬ Function.Surjective f := fun h ↦ hf h.bijective_of_finite
    unfold Function.Surjective at hns
    push Not at hns
    obtain ⟨j, hj⟩ := hns
    let p (η : Fin d → Bool) := walsh univ η * ∏ i, sign (η (f i))
    have he := average_equiv (flip j) p
    have hFlip (η : Fin d → Bool) : p (flip j η) = - p η := by
      have hProd : (∏ i, sign ((flip j η) (f i))) = ∏ i, sign (η (f i)) :=
        prod_congr rfl fun i _ ↦ congrArg sign (flip_other (hj i) η)
      unfold p
      rw [hProd, walsh_flip, ite_eq_left (mem_univ j), neg_mul]
    simp_rw [hFlip, average, sum_neg_distrib, neg_div] at he
    change average p = 0
    change -average p = average p at he
    linarith only [he]

/-- The unscaled polarization identity for a product of d coordinates. -/
theorem average_signSum_pow_polarization {d : ℕ} (y : Fin d → ℝ) :
    average (fun η ↦ walsh univ η * (∑ i, sign (η i)*y i)^d) =
      (d.factorial : ℝ) * ∏ i, y i := by
  have hPow (η : Fin d → Bool) :
      (∑ i, sign (η i)*y i)^d = ∑ f : Fin d → Fin d, ∏ i, sign (η (f i))*y (f i) := by
    have h := Fintype.prod_sum (fun (_ : Fin d) (i : Fin d) ↦ sign (η i)*y i)
    simpa only [prod_const, card_univ, Fintype.card_fin] using h
  have hFactor (f : Fin d → Fin d) (η : Fin d → Bool) :
      walsh univ η * (∏ i, sign (η (f i))*y (f i)) =
        (∏ i, y (f i)) * (walsh univ η * ∏ i, sign (η (f i))) := by
    rw [prod_mul_distrib]
    ring
  simp_rw [hPow, mul_sum, hFactor, average_sum, average_mul_left, average_polarization_signs, mul_ite, mul_zero, mul_one]
  rw [← sum_filter]
  have hTerm (f : Fin d → Fin d) (hf : f ∈ univ.filter Function.Bijective) :
      (∏ i, y (f i)) = ∏ i, y i := Equiv.prod_comp (Equiv.ofBijective f (mem_filter.mp hf).2) y
  rw [sum_congr rfl hTerm, sum_const, nsmul_eq_mul]
  let e : {f : Fin d → Fin d // Function.Bijective f} ≃ Equiv.Perm (Fin d) :=
    { toFun := fun f ↦ Equiv.ofBijective f.val f.property
      invFun := fun f ↦ ⟨f, f.bijective⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ Equiv.ext fun _ ↦ rfl }
  have hCard : (univ.filter (Function.Bijective (α := Fin d) (β := Fin d))).card = d.factorial := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
  rw [hCard]

/-- A monomial is a signed average of powers of combinations whose
coefficient absolute values sum to one. -/
theorem prod_eq_polarized_average {d : ℕ} (y : Fin d → ℝ) :
    (∏ i, y i) = (d : ℝ)^d / d.factorial *
      average (fun η ↦ walsh univ η * ((∑ i, sign (η i)*y i)/(d : ℝ))^d) := by
  cases d with
  | zero => simp [walsh]
  | succ d =>
    have hδ : ((d+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hF : (((d+1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have h (η : Fin (d+1) → Bool) :
        walsh univ η * ((∑ i, sign (η i)*y i)/((d+1 : ℕ) : ℝ))^(d+1) =
          (((d+1 : ℕ) : ℝ)^(d+1))⁻¹ * (walsh univ η * (∑ i, sign (η i)*y i)^(d+1)) := by
      rw [div_pow, div_eq_mul_inv]
      ring
    simp_rw [h, average_mul_left, average_signSum_pow_polarization]
    field_simp

end LovaszTheta.Circulant
