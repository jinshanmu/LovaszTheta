module

public import LovaszTheta.BranchingWeights
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.BigOperators

/-!
# Counting types by depth-first traversal

The opening and closing marks of each node form a binary word.
The decoder reads one tree and permits arbitrary trailing bits.
Padding to twice the size cutoff therefore gives an injection.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.PlaneTree

/-- Open a node, traverse its ordered children, and close it. -/
def traversal : PlaneTree → List Bool
  | .mk _ c => false :: (List.ofFn (fun i ↦ traversal (c i))).flatten ++ [true]

private lemma sum_lengths_ofFn {j : ℕ} (f : Fin j → List Bool) :
    (List.ofFn f).flatten.length = ∑ i, (f i).length := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.ofFn_succ, List.flatten_cons, List.length_append, Fin.sum_univ_succ, ih]

lemma length_traversal (t : PlaneTree) : t.traversal.length = 2*t.population := by
  induction t with
  | mk j c ih =>
    rw [traversal, List.length_append, List.length_cons, sum_lengths_ofFn]
    simp only [List.length_singleton, ih, population_mk, mul_add, mul_one, mul_sum]
    omega

/-- Close a node whose children are already listed in plane order. -/
def ofChildren (c : List PlaneTree) : PlaneTree :=
  WType.mk c.length (fun i ↦ c[i])

lemma ofChildren_ofFn {j : ℕ} (c : Fin j → PlaneTree) :
    ofChildren (List.ofFn c) = WType.mk j c := by
  apply (WType.equivSigma _).injective
  apply List.ofFn_inj'.mp
  exact List.ofFn_getElem (xs := List.ofFn c)

/-- Read a single tree with a stack of its open nodes. The children
recorded on the stack are in reverse order. -/
def decode (bits : List Bool) (stack : List (List PlaneTree)) : Option PlaneTree :=
  match bits, stack with
  | false :: rest, s => decode rest ([] :: s)
  | true :: _, [c] => some (ofChildren c.reverse)
  | true :: rest, c :: p :: s => decode rest ((ofChildren c.reverse :: p) :: s)
  | _, _ => none

private lemma decode_forest (forest : List PlaneTree)
    (h : ∀ t ∈ forest, ∀ rest p s, decode (traversal t ++ rest) (p :: s) = decode rest ((t :: p) :: s))
    (p : List PlaneTree) (s : List (List PlaneTree)) (rest : List Bool) :
    decode ((forest.map traversal).flatten ++ rest) (p :: s) =
      decode rest ((forest.reverse ++ p) :: s) := by
  induction forest generalizing p with
  | nil => simp
  | cons t forest ih =>
    rw [List.map_cons, List.flatten_cons, List.append_assoc, h t List.mem_cons_self,
      ih (fun u hu ↦ h u (List.mem_cons_of_mem t hu))]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma decode_child (t : PlaneTree) (rest : List Bool) (p : List PlaneTree)
    (s : List (List PlaneTree)) :
    decode (traversal t ++ rest) (p :: s) = decode rest ((t :: p) :: s) := by
  induction t generalizing rest p s with
  | mk j c ih =>
    simp only [traversal, List.append_assoc, List.cons_append, decode]
    change decode ((List.ofFn (traversal ∘ c)).flatten ++ (true :: rest)) ([] :: p :: s) = _
    rw [← List.map_ofFn, decode_forest (List.ofFn c) (by
      intro u hu
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      exact ih i)]
    simp only [List.append_nil, List.reverse_reverse, decode, ofChildren_ofFn]

/-- The decoder recovers the first tree regardless of trailing bits. -/
lemma decode_traversal (t : PlaneTree) (rest : List Bool) :
    decode (t.traversal ++ rest) [] = some t := by
  cases t with
  | mk j c =>
    simp only [traversal, List.append_assoc, List.cons_append, decode]
    change decode ((List.ofFn (traversal ∘ c)).flatten ++ (true :: rest)) [[]] = _
    rw [← List.map_ofFn, decode_forest (List.ofFn c) (by
      intro u hu
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      exact decode_child (c i))]
    simp only [List.append_nil, List.reverse_reverse, decode, ofChildren_ofFn]

/-- The traversal padded to the specified size cutoff. -/
def paddedTraversal (D : ℕ) (t : {t : PlaneTree // t.population ≤ D}) : List.Vector Bool (2*D) :=
  ⟨t.val.traversal ++ List.replicate (2*D-t.val.traversal.length) false, by
    rw [List.length_append, List.length_replicate, length_traversal]
    omega⟩

lemma paddedTraversal_injective (D : ℕ) : Function.Injective (paddedTraversal D) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg (fun w : List.Vector Bool (2*D) ↦ decode w.val []) h
  apply Option.some.inj
  simpa only [paddedTraversal, decode_traversal] using he

noncomputable instance (D : ℕ) : Fintype {t : PlaneTree // t.population ≤ D} :=
  Fintype.ofInjective (paddedTraversal D) (paddedTraversal_injective D)

/-- There are at most four to the power of the cutoff plane trees. -/
theorem card_population_le (D : ℕ) :
    Fintype.card {t : PlaneTree // t.population ≤ D} ≤ 4^D := by
  have h := Fintype.card_le_of_injective (paddedTraversal D) (paddedTraversal_injective D)
  simpa only [card_vector, Fintype.card_bool, pow_mul, show 2^2 = 4 by decide] using h

end LovaszTheta.Circulant.PlaneTree
