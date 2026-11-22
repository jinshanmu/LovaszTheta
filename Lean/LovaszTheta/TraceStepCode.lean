module

public import LovaszTheta.TraceWaitingState

/-!
# The code for one block

A marked block records its shape and the old names of its roles.
Each step contributes one bit. The waiting state determines
whether the bit records a return destination or the next type.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ} {c : TraceBlocks V (l+2)}

/-- Names visible at all slots of a processed prefix. -/
noncomputable def knownSlot (c : TraceBlocks V (l+2)) (v k : ℕ) (s : Name l v) : Option (Name l v) :=
  if (coordinates s).1.val < k then
    (exposedLabel c (coordinates s).1 (coordinates s).2).bind (priorName c v k)
  else none

lemma knownSlot_of_not_lt {k : ℕ} {s : Name l v} (h : ¬(coordinates s).1.val < k) :
    knownSlot c v k s = none := by rw [knownSlot,ite_eq_right h]

lemma knownSlot_eq_priorName {k : ℕ} {i : Fin (l+2)} {p : Fin (v+2)} {u : V}
    (hi : i.val < k) (h : exposedLabel c i p = some u) :
    knownSlot c v k (slot i p) = priorName c v k u := by
  rw [knownSlot,coordinates_slot]
  simp only [hi,ite_true,h,Option.bind_some]

lemma knownSlot_succ_current {i : Fin (l+2)} {p : Fin (v+2)} :
    knownSlot c v (i.val+1) (slot i p) =
      (exposedLabel c i p).map (fun u ↦ (priorName c v i.val u).getD (slot i p)) := by
  cases h : exposedLabel c i p with
  | none =>
    rw [knownSlot,coordinates_slot]
    simp only [Nat.lt_succ_self,ite_true,h,Option.bind_none,Option.map_none]
  | some u =>
    rw [knownSlot_eq_priorName (Nat.lt_succ_self _) h,priorName_succ_of_exposedLabel h,Option.map_some]

lemma priorName_ne_none_of_exposed {k : ℕ} {i : Fin (l+2)} {p : Fin (v+2)} {u : V}
    (hi : i.val < k) (h : exposedLabel c i p = some u) : priorName c v k u ≠ none := by
  intro he
  apply (priorName_eq_none_iff _ _ _ _).mp he
  refine ⟨slot i p,mem_priorSlots.mpr ?_⟩
  rw [coordinates_slot]
  exact ⟨hi,h⟩

lemma knownSlot_persist {j k : ℕ} {s : Name l v} (hj : j ≤ k) (h : (coordinates s).1.val < j) :
    knownSlot c v k s = knownSlot c v j s := by
  unfold knownSlot
  rw [ite_eq_left (h.trans_le hj),ite_eq_left h]
  cases he : exposedLabel c (coordinates s).1 (coordinates s).2 with
  | none => rfl
  | some u =>
    simp only [Option.bind_some]
    cases ha : priorName c v j u with
    | none => exact (priorName_ne_none_of_exposed h he ha).elim
    | some n => exact priorName_persist hj ha

lemma knownSlot_zero (c : TraceBlocks V (l+2)) (s : Name l v) : knownSlot c v 0 s = none :=
  knownSlot_of_not_lt (Nat.not_lt_zero _)

/-- The step has a private pair returning there. -/
def privateReturnAt (c : TraceBlocks V (l+2)) (k : ℕ) : Prop :=
  ∃ i j : Fin (l+2), j.val = k ∧ c.privatePair i j

lemma privateReturnAt_iff (c : TraceBlocks V (l+2)) (j : Fin (l+2)) :
    privateReturnAt c j.val ↔ ∃ i, c.privatePair i j := by
  constructor
  · rintro ⟨i,k,hk,h⟩
    exact ⟨i,(Fin.ext hk) ▸ h⟩
  · rintro ⟨i,h⟩
    exact ⟨i,j,rfl,h⟩

lemma not_privateReturnAt_zero (c : TraceBlocks V (l+2)) : ¬privateReturnAt c 0 := by
  rintro ⟨i,j,hj,h⟩
  have h' : i.val < j.val := h.1.1
  omega

/-- Another waiting pair contains the exposed endpoint other than this return's start. -/
def otherWaiting (c : TraceBlocks V (l+2)) (i j : Fin (l+2)) : Prop :=
  ∃ p q, c.waitingPair j p q ∧ p ≠ i ∧
    otherEndpoint (c.block i) (c.block j).left ∈ (c.block p).vertices

/-- The bit records whichever choice the state leaves open. -/
noncomputable def stepBit (c : TraceBlocks V (l+2)) (j : Fin (l+2)) : Bool :=
  if h : ∃ i, c.privatePair i j then
    if c.otherWaiting h.choose j then decide (c.privateReturnAt (j.val+1))
    else decide ((c.block j).right ≠ otherEndpoint (c.block h.choose) (c.block j).left)
  else decide (c.privateReturnAt (j.val+1))

lemma stepBit_eq_nextType_of_no_return {j : Fin (l+2)} (hj : ¬c.privateReturnAt j.val) :
    stepBit c j = decide (c.privateReturnAt (j.val+1)) := by
  have h : ¬∃ i, c.privatePair i j := fun he ↦ hj ((privateReturnAt_iff c j).mpr he)
  rw [stepBit,dite_eq_right h]

lemma stepBit_eq_of_return {i j : Fin (l+2)} (hp : c.privatePair i j) :
    stepBit c j = if c.otherWaiting i j then decide (c.privateReturnAt (j.val+1))
      else decide ((c.block j).right ≠ otherEndpoint (c.block i) (c.block j).left) := by
  have h : ∃ p, c.privatePair p j := ⟨i,hp⟩
  rw [stepBit,dite_eq_left h]
  have hEq : h.choose = i := c.exactPair_left_unique h.choose_spec.1 hp.1
  rw [hEq]

/-- The exposed information from a block in the equality-pattern code. -/
structure StepCode (l v : ℕ) where
  /-- The shape is included precisely at marked blocks. -/
  markedShape : Option BasicShape
  /-- References to prior names at the marked block's roles. -/
  reference : Fin (v+2) → Option (Name l v)
  /-- The step's binary choice. -/
  bit : Bool

/-- The code of one step, with an empty reference list at unmarked blocks. -/
noncomputable def encodeStep (c : TraceBlocks V (l+2)) (v : ℕ) (j : Fin (l+2)) : StepCode l v where
  markedShape := if j ∈ c.markedPositions then some (c.block j).shape else none
  reference := fun p ↦ if j ∈ c.markedPositions then
    (exposedLabel c j p).bind (priorName c v j.val) else none
  bit := stepBit c j

end TraceBlocks

end LovaszTheta.Independent
