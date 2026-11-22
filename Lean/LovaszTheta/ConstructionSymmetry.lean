module

public import LovaszTheta.CoefficientTrees

/-!
# Reversal and inclusion of coefficient arrays

Reversing a construction reverses the tuple of children and each
of their boundaries. Increasing the depth keeps every previous
shape and its unnormalized coefficient.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.Construction

variable {N : ℕ}

private lemma ofFn_reverse {A : Type*} {j : ℕ} (f : Fin j → A) :
    List.ofFn (fun i ↦ f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_reverse,List.getElem_ofFn,List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    simp only [Fin.val_rev,List.length_ofFn]
    omega

/-- Reverse the boundaries of every block in a construction. -/
def reverse (N : ℕ) : (h : ℕ) → Construction N h → Construction N h
  | 0,u => u
  | _+1,.inl u => .inl u
  | h+1,.inr ⟨j,w⟩ => .inr ⟨j,fun i ↦ reverse N h (w i.rev)⟩

lemma reverse_involutive (N h : ℕ) : Function.Involutive (reverse N h) := by
  induction h with
  | zero => exact fun _ ↦ rfl
  | succ h ih =>
    intro t
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · have he : (fun i ↦ reverse N h (reverse N h (w i.rev.rev))) = w := by
        funext i
        rw [Fin.rev_rev,ih]
      exact congrArg (node h j) he

/-- The reversal permutation on the shapes at the given depth. -/
def reversal (N h : ℕ) : Equiv.Perm (Construction N h) :=
  (reverse_involutive N h).toPerm

@[simp]
lemma reverse_leaf (h : ℕ) : reverse N h (leaf h) = leaf h := by cases h <;> rfl

lemma shape_reverse (N h : ℕ) (t : Construction N h) :
    shape N h (reverse N h t) = (shape N h t).reverse := by
  induction h with
  | zero => exact singleEdgeShape_reverse.symm
  | succ h ih =>
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · exact singleEdgeShape_reverse.symm
    · let P := List.ofFn fun i ↦ shape N h (w i)
      let Q := List.ofFn fun i ↦ shape N h (reverse N h (w i.rev))
      have hQ : Q = Chain.reversed P := by
        unfold P Q Chain.reversed
        simp only [ih,List.map_reverse,List.map_ofFn]
        exact ofFn_reverse (fun i : Fin j.val ↦ (shape N h (w i)).reverse)
      have hP := chain_ofFn_nonempty j (fun i ↦ shape N h (w i))
      have hQ' := chain_ofFn_nonempty j (fun i ↦ shape N h (reverse N h (w i.rev)))
      have hQ'' : Chain.reversed P ≠ [] := hQ ▸ hQ'
      change Chain.close Q hQ' = (Chain.close P hP).reverse
      have close_eq {C D : Chain} (he : C = D) (hC : C ≠ []) (hD : D ≠ []) : C.close hC = D.close hD := by
        subst D
        rfl
      exact (close_eq hQ hQ' hQ'').trans (Chain.close_reversed P hP hQ'')

lemma coefficient_reverse (N h : ℕ) (t : Construction N h) :
    coefficient N h (reverse N h t) = coefficient N h t := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · change bernsteinCoefficient N j.val*(∏ i : Fin j.val, coefficient N h (reverse N h (w i.rev))) =
        bernsteinCoefficient N j.val*(∏ i, coefficient N h (w i))
      simp only [ih]
      congr 1
      exact Fintype.prod_equiv Fin.revPerm _ _ fun _ ↦ rfl

lemma normalized_reverse (N h : ℕ) (t : Construction N h) :
    normalized N h (reverse N h t) = normalized N h t := by
  rw [normalized,normalized,coefficient_reverse]

/-- Include a tree in the array one level deeper. -/
def widen (N : ℕ) : (h : ℕ) → Construction N h → Construction N (h+1)
  | 0,_ => leaf 1
  | _+1,.inl u => .inl u
  | h+1,.inr ⟨j,w⟩ => .inr ⟨j,fun i ↦ widen N h (w i)⟩

@[simp]
lemma widen_leaf (h : ℕ) : widen N h (leaf h) = leaf (h+1) := by cases h <;> rfl

lemma shape_widen (N h : ℕ) (t : Construction N h) :
    shape N (h+1) (widen N h t) = shape N h t := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · let f := fun (u : Fin j.val → BasicShape) ↦ Chain.close (List.ofFn u) (chain_ofFn_nonempty j u)
      exact congrArg f (funext fun i ↦ ih (w i))

lemma widen_injective (N h : ℕ) : Function.Injective (widen N h) := by
  intro x y he
  apply shape_injective N h
  rw [← shape_widen N h x,← shape_widen N h y,he]

lemma coefficient_widen (N h : ℕ) (t : Construction N h) :
    coefficient N (h+1) (widen N h t) = coefficient N h t := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · change bernsteinCoefficient N j.val*(∏ i, coefficient N (h+1) (widen N h (w i))) =
        bernsteinCoefficient N j.val*(∏ i, coefficient N h (w i))
      simp only [ih]

lemma widen_reverse (N h : ℕ) (t : Construction N h) :
    widen N h (reverse N h t) = reverse N (h+1) (widen N h t) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · exact congrArg (node (h+1) j) (funext fun i ↦ ih (w i.rev))

lemma sum_sq_widen_image (N h : ℕ) :
    (∑ t ∈ univ.image (widen N h), (coefficient N (h+1) t)^2) = mass N h := by
  rw [sum_image (widen_injective N h).injOn]
  simp only [coefficient_widen,mass]

/-- Each depth retains all the squared mass from the previous depth. -/
theorem mass_mono (N : ℕ) : Monotone (mass N) := by
  apply monotone_nat_of_le_succ
  intro h
  rw [← sum_sq_widen_image N h]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ sq_nonneg _)

end LovaszTheta.Independent.Construction
