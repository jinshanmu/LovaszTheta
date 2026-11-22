module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Tactic

/-!
# Counting solutions to a single linear congruence

Fix all variables except one with a nonzero integer coefficient.
On representatives from zero to the modulus minus one, the
quotient of the coefficient times the representative determines
the solution once the remainder is fixed.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

private lemma card_natCast_mul_fibre_le {a : ℕ} (ha : 0 < a) (b : ZMod n) :
    Fintype.card {x : ZMod n // (a : ZMod n) * x = b} ≤ a := by
  let X := {x : ZMod n // (a : ZMod n) * x = b}
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hSmall (x : X) : a * x.val.val / n < a := by
    apply (Nat.div_lt_iff_lt_mul hn).mpr
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x.val) ha
  let code (x : X) : Fin a := ⟨a * x.val.val / n, hSmall x⟩
  have hMod (x : X) : a * x.val.val % n = b.val := by
    rw [← ZMod.val_natCast]
    apply congrArg ZMod.val
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using x.property
  have hInj : Function.Injective code := by
    intro x y he
    have hQ := congrArg Fin.val he
    change a * x.val.val / n = a * y.val.val / n at hQ
    have hProd : a * x.val.val = a * y.val.val := by
      calc
        _ = a * x.val.val % n + n * (a * x.val.val / n) := (Nat.mod_add_div _ _).symm
        _ = a * y.val.val % n + n * (a * y.val.val / n) := by rw [hMod x, hMod y, hQ]
        _ = _ := Nat.mod_add_div _ _
    exact Subtype.ext ((ZMod.val_injective n) (mul_left_cancel₀ ha.ne' hProd))
  exact (Fintype.card_le_of_injective code hInj).trans_eq (Fintype.card_fin a)

/-- Multiplication by a nonzero integer has at most its absolute value
many preimages in any positive modulus. -/
theorem card_intCast_mul_fibre_le {a : ℤ} (ha : a ≠ 0) (b : ZMod n) :
    Fintype.card {x : ZMod n // (a : ZMod n) * x = b} ≤ a.natAbs := by
  cases a with
  | ofNat a =>
    have ha' : a ≠ 0 := fun h ↦ ha (congrArg Int.ofNat h)
    change Fintype.card {x : ZMod n // ((a : ℤ) : ZMod n) * x = b} ≤ a
    simpa only [Int.cast_natCast] using card_natCast_mul_fibre_le (Nat.pos_of_ne_zero ha') b
  | negSucc a =>
    have hCast : (Int.negSucc a : ZMod n) = -((a+1 : ℕ) : ZMod n) := by
      push_cast
      ring
    let map (x : {x : ZMod n // (Int.negSucc a : ZMod n) * x = b}) :
        {x : ZMod n // ((a+1 : ℕ) : ZMod n) * x = -b} := ⟨x.val, by
      have hx : -((a+1 : ℕ) : ZMod n) * x.val = b :=
        (congrArg (fun z : ZMod n ↦ z * x.val) hCast.symm).trans x.property
      simpa only [neg_mul, neg_neg] using congrArg (fun z : ZMod n ↦ -z) hx⟩
    have hInj : Function.Injective map := fun _ _ he ↦ Subtype.ext
      (congrArg (fun y : {x : ZMod n // ((a+1 : ℕ) : ZMod n) * x = -b} ↦ y.val) he)
    exact (Fintype.card_le_of_injective map hInj).trans
      (card_natCast_mul_fibre_le (Nat.succ_pos _) (-b))

/-- A nonzero coefficient at i gives the uniform count of assignments
satisfying a prescribed linear congruence. -/
theorem card_linear_congruence_fibre_le {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (i : I) (ha : a i ≠ 0) (b : ZMod n) :
    Fintype.card {x : I → ZMod n // ∑ j, (a j : ZMod n) * x j = b} ≤
      (a i).natAbs * n^(Fintype.card I - 1) := by
  let X := {x : I → ZMod n // ∑ j, (a j : ZMod n) * x j = b}
  let R := (univ : Finset I).erase i
  let rest (x : X) : R → ZMod n := fun j ↦ x.val j.val
  let rhs (z : R → ZMod n) := b - ∑ j : R, (a j.val : ZMod n) * z j
  let Y (z : R → ZMod n) := {u : ZMod n // (a i : ZMod n) * u = rhs z}
  have hPivot (x : X) : (a i : ZMod n) * x.val i = rhs (rest x) := by
    change (a i : ZMod n) * x.val i = b - ∑ j : R, (a j.val : ZMod n) * x.val j.val
    rw [sum_coe_sort R (fun j : I ↦ (a j : ZMod n) * x.val j), eq_sub_iff_add_eq, add_comm]
    exact (sum_erase_add univ (fun j ↦ (a j : ZMod n) * x.val j) (mem_univ i)).trans x.property
  let code (x : X) : Σ z : R → ZMod n, Y z := ⟨rest x, ⟨x.val i, hPivot x⟩⟩
  have hInj : Function.Injective code := by
    intro x y he
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j
      exact congrArg (fun c : Σ z : R → ZMod n, Y z ↦ c.2.val) he
    · exact congrFun (congrArg Sigma.fst he) ⟨j, mem_erase.mpr ⟨h, mem_univ _⟩⟩
  calc
    Fintype.card X ≤ Fintype.card (Σ z : R → ZMod n, Y z) := Fintype.card_le_of_injective code hInj
    _ = ∑ z : R → ZMod n, Fintype.card (Y z) := Fintype.card_sigma
    _ ≤ ∑ _z : R → ZMod n, (a i).natAbs :=
      sum_le_sum fun _ _ ↦ card_intCast_mul_fibre_le ha _
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe,
        card_erase_of_mem (mem_univ i), card_univ, Nat.mul_comm]
      rfl

end LovaszTheta.Circulant
