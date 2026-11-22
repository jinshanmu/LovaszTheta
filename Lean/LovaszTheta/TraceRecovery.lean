module

public import LovaszTheta.CycleChange

/-!
# Recovering equality of all labels

Unexposed labels have a first occurrence in one forward block.
An internal label either remains private or is exposed as the
destination of the matched return. This distinguishes all label
classes after the finite code and forward shapes have been fixed.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ} {c d : TraceBlocks V (l+2)}

/-- The label at a padded vertex role, including private labels. -/
noncomputable def fullLabel (c : TraceBlocks V (l+2)) (i : Fin (l+2)) (p : Fin (v+2)) : Option V :=
  if h : p.val < (c.block i).shape.additionalVertices+2 then some ((c.block i).label ⟨p.val,h⟩) else none

lemma fullLabel_eq_some_iff {i : Fin (l+2)} {p : Fin (v+2)} {u : V} :
    fullLabel c i p = some u ↔ ∃ r : Fin ((c.block i).shape.additionalVertices+2),
      r.val = p.val ∧ (c.block i).label r = u := by
  unfold fullLabel
  split_ifs with h
  · constructor
    · exact fun he ↦ ⟨⟨p.val,h⟩,rfl,Option.some.inj he⟩
    · rintro ⟨a,ha,he⟩
      exact congrArg some ((congrArg (c.block i).label (Fin.ext ha.symm)).trans he)
  · constructor
    · intro he
      cases he
    · rintro ⟨a,ha,_⟩
      exact (h (ha ▸ a.isLt)).elim

lemma fullLabel_mem_vertices {i : Fin (l+2)} {p : Fin (v+2)} {u : V}
    (h : fullLabel c i p = some u) : u ∈ (c.block i).vertices := by
  obtain ⟨r,_,he⟩ := fullLabel_eq_some_iff.mp h
  exact ((c.block i).mem_vertices_iff u).mpr ⟨r,he⟩

lemma fullLabel_roles_unique {i : Fin (l+2)} {p q : Fin (v+2)} {u : V}
    (hp : fullLabel c i p = some u) (hq : fullLabel c i q = some u) : p = q := by
  obtain ⟨a,ha,he⟩ := fullLabel_eq_some_iff.mp hp
  obtain ⟨b,hb,he'⟩ := fullLabel_eq_some_iff.mp hq
  exact Fin.ext (ha.symm.trans ((congrArg Fin.val ((c.block i).label.injective (he.trans he'.symm))).trans hb))

private lemma exposed_eq_fullLabel_of_marked {i : Fin (l+2)} (hi : i ∈ c.markedPositions) (p : Fin (v+2)) :
    exposedLabel c i p = fullLabel c i p := by rw [exposedLabel,ite_eq_left hi,fullLabel]

private lemma fullLabel_boundary (c : TraceBlocks V (l+2)) (i : Fin (l+2)) :
    fullLabel (v := v) c i 0 = some (c.block i).left ∧
      fullLabel (v := v) c i 1 = some (c.block i).right := by
  constructor
  · exact fullLabel_eq_some_iff.mpr ⟨0,rfl,rfl⟩
  · exact fullLabel_eq_some_iff.mpr ⟨1,by simp,rfl⟩

private lemma left_or_right_of_unmarked_exposed {i : Fin (l+2)} {p : Fin (v+2)} {u : V}
    (hi : i ∉ c.markedPositions) (hu : exposedLabel c i p = some u) :
    u = (c.block i).left ∨ u = (c.block i).right := by
  rw [exposedLabel,ite_eq_right hi] at hu
  split_ifs at hu
  · exact Or.inl (Option.some.inj hu).symm
  · exact Or.inr (Option.some.inj hu).symm

/-- A visible label uses its exposure name. A private label uses the slot of its first occurrence. -/
def LabelRepresentation (c : TraceBlocks V (l+2)) (v : ℕ) (u : V)
    (tag : Name l v ⊕ Name l v) : Prop :=
  match tag with
  | Sum.inl s => priorName c v (l+2) u = some s
  | Sum.inr s => priorName c v (l+2) u = none ∧
      ∃ i p, s = slot i p ∧ fullLabel c i p = some u ∧ ¬c.Earlier i u

lemma label_eq_iff_tag_eq {u w : V} {a b : Name l v ⊕ Name l v}
    (ha : LabelRepresentation c v u a) (hb : LabelRepresentation c v w b) : u = w ↔ a = b := by
  cases a with
  | inl s =>
    cases b with
    | inl t =>
      constructor
      · rintro rfl
        exact congrArg Sum.inl (Option.some.inj (ha.symm.trans hb))
      · intro he
        have he' := Sum.inl.inj he
        subst t
        exact eq_of_priorName_eq_some ha hb
    | inr t =>
      obtain ⟨hn,_⟩ := hb
      change priorName c v (l+2) u = some s at ha
      exact iff_of_false (fun h ↦ by rw [h,hn] at ha; cases ha) (by simp)
  | inr s =>
    cases b with
    | inl t =>
      obtain ⟨hn,_⟩ := ha
      change priorName c v (l+2) w = some t at hb
      exact iff_of_false (fun h ↦ by rw [← h,hn] at hb; cases hb) (by simp)
    | inr t =>
      obtain ⟨_,i,p,rfl,ha,hEi⟩ := ha
      obtain ⟨_,j,q,rfl,hb,hEj⟩ := hb
      constructor
      · intro he
        subst w
        have hIJ : i = j := by
          by_contra hNe
          rcases lt_or_gt_of_ne hNe with hlt | hgt
          · exact hEj ⟨i,hlt,fullLabel_mem_vertices ha⟩
          · exact hEi ⟨j,hgt,fullLabel_mem_vertices hb⟩
        subst j
        rw [fullLabel_roles_unique ha hb]
      · intro he
        have he' := congrArg coordinates (Sum.inr.inj he)
        simp only [coordinates_slot] at he'
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he'
        exact Option.some.inj (ha.symm.trans hb)

lemma exists_shared_representation_of_exposed (he : PrefixAgreement c d v (l+2))
    {i : Fin (l+2)} {p : Fin (v+2)} {u w : V}
    (hc : exposedLabel c i p = some u) (hd : exposedLabel d i p = some w) :
    ∃ tag, LabelRepresentation c v u tag ∧ LabelRepresentation d v w tag := by
  have h := he.names (slot i p)
  rw [knownSlot_eq_priorName i.isLt hc,knownSlot_eq_priorName i.isLt hd] at h
  cases hn : priorName c v (l+2) u with
  | none => exact (priorName_ne_none_of_exposed i.isLt hc hn).elim
  | some s => exact ⟨Sum.inl s,hn,h.symm.trans hn⟩

/-- Except for the destination, an internal label of a private pair is never exposed. -/
theorem internal_label_is_private (h : c.RepeatedEdges) {i j : Fin (l+2)}
    (hp : c.privatePair i j) {p : Fin (v+2)} {u : V}
    (hFull : fullLabel c i p = some u) (hLeft : u ≠ (c.block i).left) (hRight : u ≠ (c.block i).right)
    (hDest : u ≠ (c.block j).right) : LabelRepresentation c v u (Sum.inr (slot i p)) := by
  have hPair := forward_return_of_exactPair h hp.1
  have hMark := notMem_markedPositions_of_privatePair h hp
  have hU := fullLabel_mem_vertices hFull
  have hNo : ¬c.Earlier i u := fun he ↦ hLeft (hPair.1 u hU he)
  refine ⟨(priorName_eq_none_iff _ _ _ _).mpr ?_,i,p,rfl,hFull,hNo⟩
  rintro ⟨s,hs⟩
  have hS := (mem_priorSlots.mp hs).2
  let k := (coordinates s).1
  have hK : u ∈ (c.block k).vertices := mem_vertices_of_exposedLabel hS
  rcases lt_trichotomy k i with hlt | he | hgt
  · exact hNo ⟨k,hlt,hK⟩
  · change exposedLabel c k (coordinates s).2 = some u at hS
    rw [he] at hS
    exact (left_or_right_of_unmarked_exposed hMark.1 hS).elim hLeft hRight
  · rcases lt_trichotomy k j with hlt | he | hgt'
    · exact hp.2 u ⟨hU,hLeft,hRight,k,hgt,hlt,hK⟩
    · change exposedLabel c k (coordinates s).2 = some u at hS
      rw [he] at hS
      rcases left_or_right_of_unmarked_exposed hMark.2 hS with hl | hr
      · rcases return_left_is_endpoint hp with h₁ | h₂
        · exact hLeft (hl.trans h₁)
        · exact hRight (hl.trans h₂)
      · exact hDest hr
    · have hU' : u ∈ (c.block j).vertices := (LabeledBlock.vertices_eq_of_graph_eq hp.1.2.2.2.1) ▸ hU
      exact hDest (hPair.2 u hU' ⟨k,hgt',hK⟩)

end TraceBlocks

end LovaszTheta.Independent
