module

public import LovaszTheta.CharacterMoments
public import LovaszTheta.DescendantSupport

/-!
# Uniform root and descendant residues

A leaf inside a proper subtree and a leaf outside it give the two
unit pivots for the root and subtree sums. Under the uniform leaf law
the two sums are independent uniform residues.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

private lemma average_prod_mul {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) :
    average (fun x : A × B ↦ f x.1 * g x.2) = average f * average g := by
  unfold average
  rw [Fintype.card_prod, Nat.cast_mul, div_mul_div_comm, Fintype.sum_prod_type]
  simp only [sum_mul, mul_sum]
  congr 1
  exact sum_comm

private lemma average_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (h : Function.Surjective f) (g : B → ℝ) :
    average (fun a ↦ g (f a)) = average g := by
  choose r hr using h
  let K := {a : A // f a = 0}
  let : Nonempty K := ⟨⟨0, f.map_zero⟩⟩
  let e : B × K ≃ A :=
    { toFun := fun p ↦ p.2.val + r p.1
      invFun := fun a ↦ (f a, ⟨a - r (f a), by rw [f.map_sub, hr, sub_self]⟩)
      left_inv := by
        rintro ⟨b, k⟩
        have he : f (k.val + r b) = b := by rw [f.map_add, k.property, hr, zero_add]
        refine Prod.ext he (Subtype.ext ?_)
        change k.val + r b - r (f (k.val + r b)) = k.val
        rw [he, add_sub_cancel_right]
      right_inv := fun a ↦ sub_add_cancel _ _ }
  rw [← average_equiv e (fun a ↦ g (f a))]
  have hVal (p : B × K) : g (f (e p)) = g p.1 * 1 := by
    change g (f (p.2.val + r p.1)) = _
    rw [f.map_add, p.2.property, hr, zero_add, mul_one]
  simp_rw [hVal]
  simpa only [average_const, mul_one] using average_prod_mul g (fun _ : K ↦ 1)

variable {n : ℕ} [NeZero n]

private def pairedSums {I : Type*} (A B : Finset I) : (I → ZMod n) →+ (ZMod n × ZMod n) where
  toFun f := (∑ i ∈ A, f i, ∑ i ∈ B, f i)
  map_zero' := by simp
  map_add' := by intro f g; ext <;> simp [sum_add_distrib]

/-- Two nested leaf sums are jointly uniform when each of the inner
set and its complement in the outer set is nonempty. -/
theorem average_pairedSums {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Finset I) (hBA : B ⊆ A) (hB : B.Nonempty) (hAB : (A \ B).Nonempty)
    (g : ZMod n × ZMod n → ℝ) :
    average (fun f : I → ZMod n ↦ g (∑ i ∈ A, f i, ∑ i ∈ B, f i)) = average g := by
  obtain ⟨i, hi⟩ := hB
  obtain ⟨j, hj⟩ := hAB
  obtain ⟨hjA, hjB⟩ := mem_sdiff.mp hj
  change average (fun f : I → ZMod n ↦ g (pairedSums A B f)) = average g
  refine average_comp_surjective_addHom (pairedSums A B) ?_ g
  intro z
  let f := (Pi.single i z.2 : I → ZMod n) + Pi.single j (z.1 - z.2)
  have hiA := hBA hi
  refine ⟨f, Prod.ext ?_ ?_⟩
  · change (∑ a ∈ A, f a) = z.1
    simp only [f, Pi.add_apply, sum_add_distrib, sum_pi_single', hiA, hjA, ite_true]
    abel
  · change (∑ a ∈ B, f a) = z.2
    simp only [f, Pi.add_apply, sum_add_distrib, sum_pi_single', hi, hjB, ite_true, ite_false, add_zero]

/-- The sum of any nonempty set of uniform leaves is a uniform residue. -/
theorem average_leafSum {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) (g : ZMod n → ℝ) :
    average (fun f : I → ZMod n ↦ g (∑ i ∈ A, f i)) = average g := by
  let sumHom : (I → ZMod n) →+ ZMod n :=
    { toFun := fun f ↦ ∑ i ∈ A, f i
      map_zero' := by simp
      map_add' := fun f g ↦ by simp [sum_add_distrib] }
  change average (fun f ↦ g (sumHom f)) = average g
  refine average_comp_surjective_addHom sumHom ?_ g
  obtain ⟨i, hi⟩ := hA
  intro r
  exact ⟨Pi.single i r, by simp [sumHom, hi]⟩

/-- In the unrestricted leaf sum, the product of the root character and
a proper-node character has mean zero at a nonzero root frequency. -/
theorem average_root_nonroot_character_eq_zero (T : RootedTree) (u : T.Node) (hu : u ≠ T.root)
    (k j : ZMod n) (hk : k ≠ 0) :
    average (fun f : T.Leaf → ZMod n ↦
      (ZMod.stdAddChar (-(T.residue f T.root * k))).re *
        (ZMod.stdAddChar (-(T.residue f u * j))).re) = 0 := by
  have hAnc : T.IsAncestor T.root u := T.exists_iterate_parent_eq_root u
  have hSub := hAnc.descendantLeaves_ssubset hu.symm
  have hRest : (T.descendantLeaves T.root \ T.descendantLeaves u).Nonempty :=
    Finset.sdiff_nonempty.mpr (not_le_of_gt hSub)
  let g (a : ZMod n × ZMod n) :=
    (ZMod.stdAddChar (-(a.1 * k))).re * (ZMod.stdAddChar (-(a.2 * j))).re
  change average (fun f : T.Leaf → ZMod n ↦
    g (∑ i ∈ T.descendantLeaves T.root, f i, ∑ i ∈ T.descendantLeaves u, f i)) = _
  rw [average_pairedSums _ _ hSub.le (T.descendantLeaves_nonempty u) hRest]
  have hChar : average (fun a : ZMod n ↦ (ZMod.stdAddChar (-(a * k))).re) = 0 := by
    simp only [average, re_stdAddChar_neg, mul_comm _ k, sum_re_stdAddChar_mul, hk, ite_false, zero_div]
  unfold g
  rw [average_prod_mul (fun a : ZMod n ↦ (ZMod.stdAddChar (-(a*k))).re)
    (fun a : ZMod n ↦ (ZMod.stdAddChar (-(a*j))).re), hChar, zero_mul]

/-- The unrestricted root-to-root character average for a regular frequency. -/
theorem average_root_character_pair (T : RootedTree) (k j : ZMod n) (hk : RegularFrequency k) :
    average (fun f : T.Leaf → ZMod n ↦
      (ZMod.stdAddChar (-(T.residue f T.root * k))).re *
        (ZMod.stdAddChar (-(T.residue f T.root * j))).re) =
      if j = k ∨ j = -k then 1 / 2 else 0 := by
  let g (r : ZMod n) :=
    (ZMod.stdAddChar (-(r * k))).re * (ZMod.stdAddChar (-(r * j))).re
  change average (fun f : T.Leaf → ZMod n ↦ g (∑ i ∈ T.descendantLeaves T.root, f i)) = _
  rw [average_leafSum _ (T.descendantLeaves_nonempty T.root) g]
  exact average_re_stdAddChar_pair k j hk

end LovaszTheta.Circulant
