module

public import LovaszTheta.WaitingPairs
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Names of exposed trace labels

A label is named by its first exposure slot. Slots are ordered by
block and then by role. Marked blocks expose all their labels, and
unmarked blocks expose only the two boundaries.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ}

/-- At most one name is needed for each padded block role. -/
abbrev Name (l v : ℕ) := Fin ((l+2)*(v+2))

/-- The name with the given block and role. -/
def slot (i : Fin (l+2)) (p : Fin (v+2)) : Name l v := finProdFinEquiv (i,p)

/-- The block and role belonging to a name. -/
def coordinates (s : Name l v) : Fin (l+2) × Fin (v+2) := finProdFinEquiv.symm s

@[simp]
lemma coordinates_slot (i : Fin (l+2)) (p : Fin (v+2)) :
    coordinates (slot i p) = (i,p) := finProdFinEquiv.symm_apply_apply _

@[simp]
lemma slot_coordinates (s : Name l v) : slot (coordinates s).1 (coordinates s).2 = s :=
  finProdFinEquiv.apply_symm_apply _

lemma slot_lt_slot_of_lt {i j : Fin (l+2)} (hij : i < j) (p q : Fin (v+2)) :
    slot i p < slot j q := by
  change p.val+(v+2)*i.val < q.val+(v+2)*j.val
  have h : i.val+1 ≤ j.val := hij
  have hMul := Nat.mul_le_mul_left (v+2) h
  rw [Nat.mul_add,Nat.mul_one] at hMul
  have hP := p.isLt
  omega

lemma name_lt_of_coordinates_lt {s t : Name l v} (h : (coordinates s).1 < (coordinates t).1) : s < t := by
  simpa only [slot_coordinates] using slot_lt_slot_of_lt h (coordinates s).2 (coordinates t).2

/-- The label exposed at a role, if that role is read by the code. -/
noncomputable def exposedLabel (c : TraceBlocks V (l+2)) (i : Fin (l+2)) (p : Fin (v+2)) : Option V :=
  if i ∈ c.markedPositions then
    if h : p.val < (c.block i).shape.additionalVertices+2 then some ((c.block i).label ⟨p.val,h⟩) else none
  else if p = 0 then some (c.block i).left else if p = 1 then some (c.block i).right else none

lemma exposedLabel_left (c : TraceBlocks V (l+2)) (i : Fin (l+2)) :
    exposedLabel (v := v) c i 0 = some (c.block i).left := by
  unfold exposedLabel
  by_cases hi : i ∈ c.markedPositions
  · have h : (0 : Fin (v+2)).val < (c.block i).shape.additionalVertices+2 := Nat.zero_lt_succ _
    rw [ite_eq_left hi,dite_eq_left h]
    rfl
  · rw [ite_eq_right hi,ite_eq_left rfl]

lemma exposedLabel_right (c : TraceBlocks V (l+2)) (i : Fin (l+2)) :
    exposedLabel (v := v) c i 1 = some (c.block i).right := by
  unfold exposedLabel
  by_cases hi : i ∈ c.markedPositions
  · have h : (1 : Fin (v+2)).val < (c.block i).shape.additionalVertices+2 := by simp
    rw [ite_eq_left hi,dite_eq_left h]
    congr 2
  · rw [ite_eq_right hi,ite_eq_right (by simp : (1 : Fin (v+2)) ≠ 0),ite_eq_left rfl]

lemma mem_vertices_of_exposedLabel {c : TraceBlocks V (l+2)} {i : Fin (l+2)}
    {p : Fin (v+2)} {u : V} (he : exposedLabel c i p = some u) : u ∈ (c.block i).vertices := by
  unfold exposedLabel at he
  by_cases hM : i ∈ c.markedPositions
  · rw [ite_eq_left hM] at he
    split_ifs at he with hP
    exact ((c.block i).mem_vertices_iff u).mpr ⟨⟨p.val,hP⟩,Option.some.inj he⟩
  · rw [ite_eq_right hM] at he
    split_ifs at he
    · exact (Option.some.inj he) ▸ (c.block i).left_mem_vertices
    · exact (Option.some.inj he) ▸ (c.block i).right_mem_vertices

lemma exposedLabel_role_unique {c : TraceBlocks V (l+2)} {i : Fin (l+2)}
    {p q : Fin (v+2)} {u : V} (hp : exposedLabel c i p = some u)
    (hq : exposedLabel c i q = some u) : p = q := by
  by_cases hi : i ∈ c.markedPositions
  · unfold exposedLabel at hp hq
    rw [ite_eq_left hi] at hp hq
    split_ifs at hp hq with hP hQ
    · exact Fin.ext (congrArg (fun a : Fin ((c.block i).shape.additionalVertices+2) ↦ a.val)
        ((c.block i).label.injective (Option.some.inj (hp.trans hq.symm))))
  · have hRole (r : Fin (v+2)) (hr : exposedLabel c i r = some u) :
        (r = 0 ∧ (c.block i).left = u) ∨ (r = 1 ∧ (c.block i).right = u) := by
      unfold exposedLabel at hr
      rw [ite_eq_right hi] at hr
      split_ifs at hr with h0 h1
      · exact Or.inl ⟨h0,Option.some.inj hr⟩
      · exact Or.inr ⟨h1,Option.some.inj hr⟩
    rcases hRole p hp with ⟨hp',hU⟩ | ⟨hp',hU⟩ <;> rcases hRole q hq with ⟨hq',hV⟩ | ⟨hq',hV⟩
    · exact hp'.trans hq'.symm
    · exact ((c.block i).left_ne_right (hU.trans hV.symm)).elim
    · exact ((c.block i).left_ne_right (hV.trans hU.symm)).elim
    · exact hp'.trans hq'.symm

/-- All exposure slots for a label strictly before a step. -/
noncomputable def priorSlots (c : TraceBlocks V (l+2)) (v k : ℕ) (u : V) : Finset (Name l v) :=
  univ.filter fun s ↦ (coordinates s).1.val < k ∧ exposedLabel c (coordinates s).1 (coordinates s).2 = some u

lemma mem_priorSlots {c : TraceBlocks V (l+2)} {k : ℕ} {u : V} {s : Name l v} :
    s ∈ priorSlots c v k u ↔ (coordinates s).1.val < k ∧
      exposedLabel c (coordinates s).1 (coordinates s).2 = some u := by
  unfold priorSlots
  rw [Finset.mem_filter]
  simp only [mem_univ,true_and]

/-- The old name of a label, determined by the first prior exposure. -/
noncomputable def priorName (c : TraceBlocks V (l+2)) (v k : ℕ) (u : V) : Option (Name l v) :=
  if h : (priorSlots c v k u).Nonempty then some ((priorSlots c v k u).min' h) else none

lemma priorName_eq_none_iff (c : TraceBlocks V (l+2)) (v k : ℕ) (u : V) :
    priorName c v k u = none ↔ ¬(priorSlots c v k u).Nonempty := by
  unfold priorName
  by_cases h : (priorSlots c v k u).Nonempty <;> simp [h]

private lemma priorName_eq_some_iff {c : TraceBlocks V (l+2)} {k : ℕ} {u : V} {s : Name l v} :
    priorName c v k u = some s ↔ s ∈ priorSlots c v k u ∧ ∀ t ∈ priorSlots c v k u, s ≤ t := by
  unfold priorName
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨min'_mem _ _,fun _ hT ↦ min'_le _ _ hT⟩
    · rintro ⟨hs,hm⟩
      exact le_antisymm (min'_le _ _ hs) (hm _ (min'_mem _ _))
  · constructor
    · exact False.elim
    · rintro ⟨hs,_⟩
      exact (h ⟨s,hs⟩).elim

lemma eq_of_priorName_eq_some {c : TraceBlocks V (l+2)} {k : ℕ} {u w : V} {s : Name l v}
    (hu : priorName c v k u = some s) (hw : priorName c v k w = some s) : u = w :=
  Option.some.inj (((mem_priorSlots.mp (priorName_eq_some_iff.mp hu).1).2).symm.trans
    (mem_priorSlots.mp (priorName_eq_some_iff.mp hw).1).2)

lemma priorName_persist {c : TraceBlocks V (l+2)} {j k : ℕ} {u : V} {s : Name l v}
    (hj : j ≤ k) (h : priorName c v j u = some s) : priorName c v k u = some s := by
  obtain ⟨hs,hm⟩ := priorName_eq_some_iff.mp h
  have hS := mem_priorSlots.mp hs
  refine priorName_eq_some_iff.mpr ⟨mem_priorSlots.mpr ⟨hS.1.trans_le hj,hS.2⟩,?_⟩
  intro t ht
  have hT := mem_priorSlots.mp ht
  by_cases hJ : (coordinates t).1.val < j
  · exact hm t (mem_priorSlots.mpr ⟨hJ,hT.2⟩)
  · exact (name_lt_of_coordinates_lt (hS.1.trans_le (le_of_not_gt hJ))).le

lemma priorName_none_of_no_earlier {c : TraceBlocks V (l+2)} {i : Fin (l+2)} {u : V}
    (hn : ¬c.Earlier i u) : priorName c v i.val u = none := by
  apply (priorName_eq_none_iff _ _ _ _).mpr
  rintro ⟨s,hs⟩
  have he := mem_priorSlots.mp hs
  exact hn ⟨(coordinates s).1,he.1,mem_vertices_of_exposedLabel he.2⟩

/-- At an exposure, keep the old name if there is one and otherwise assign the current slot. -/
theorem priorName_succ_of_exposedLabel {c : TraceBlocks V (l+2)} {i : Fin (l+2)}
    {p : Fin (v+2)} {u : V} (h : exposedLabel c i p = some u) :
    priorName c v (i.val+1) u = some ((priorName c v i.val u).getD (slot i p)) := by
  cases he : priorName c v i.val u with
  | some s => exact priorName_persist (Nat.le_succ _) he
  | none =>
    have hNone := (priorName_eq_none_iff _ _ _ _).mp he
    change priorName c v (i.val+1) u = some (slot i p)
    apply priorName_eq_some_iff.mpr
    constructor
    · apply mem_priorSlots.mpr
      rw [coordinates_slot]
      exact ⟨Nat.lt_succ_self _,h⟩
    · intro t ht
      have ht' := mem_priorSlots.mp ht
      have hEq : (coordinates t).1 = i := by
        apply Fin.ext
        have hNot : ¬(coordinates t).1.val < i.val :=
          fun hh ↦ hNone ⟨t,mem_priorSlots.mpr ⟨hh,ht'.2⟩⟩
        omega
      have hLab : exposedLabel c i (coordinates t).2 = some u := by
        have hh := ht'.2
        rw [hEq] at hh
        exact hh
      have heq := exposedLabel_role_unique h hLab
      exact (congrArg₂ slot hEq.symm heq).le.trans_eq (slot_coordinates t)

end TraceBlocks

end LovaszTheta.Independent
