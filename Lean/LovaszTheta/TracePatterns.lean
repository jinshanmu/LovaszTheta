module

public import LovaszTheta.SharpTraceExpansion
public import LovaszTheta.TracePatternRecovery

/-!
# Trace patterns and their label choices

A pattern records the shape word and the equality relation of the
padded roles. A fixed pattern can be labeled in at most one independent
way for each of its distinct labels. The defect determines the total
power of the ambient vertex count after normalization.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {J V : Type*} [Fintype J] [Fintype V] {α : J → BasicShape} {l v : ℕ}

/-- A trace word that remains after averaging the signs. -/
abbrev TraceWord (α : J → BasicShape) (V : Type*) (l : ℕ) :=
  {f : Fin (l+2) → BasicLabeling α V // stitched f ∧ evenEdgeMultiplicity f}

/-- A shape index at each step, and a Boolean equality table for padded roles. -/
abbrev TracePattern (J : Type*) (l v : ℕ) :=
  (Fin (l+2) → J) × (TraceBlocks.Name l v → TraceBlocks.Name l v → Bool)

namespace TraceWord

/-- The stitched blocks of a contributing word. -/
def blocks (w : TraceWord α V l) : TraceBlocks V (l+2) := toTraceBlocks w.val w.property.1

omit [Fintype J] [Fintype V] in
lemma repeated (w : TraceWord α V l) : w.blocks.RepeatedEdges :=
  repeatedEdges_of_evenEdgeMultiplicity w.val w.property.1 w.property.2

omit [Fintype J] [Fintype V] in
lemma shape (w : TraceWord α V l) (i : Fin (l+2)) :
    (w.blocks.block i).shape = α (w.val i).1 := rfl

/-- The actual label at a padded role. -/
noncomputable def labelAt (w : TraceWord α V l) (s : TraceBlocks.Name l v) : Option V :=
  TraceBlocks.fullLabel w.blocks (TraceBlocks.coordinates s).1 (TraceBlocks.coordinates s).2

/-- The equality pattern of a trace word. -/
noncomputable def pattern (w : TraceWord α V l) (v : ℕ) : TracePattern J l v :=
  (fun i ↦ (w.val i).1,fun s t ↦ decide (w.labelAt s = w.labelAt t))

/-- A pattern's distinct labels, using any word with that pattern. -/
noncomputable def labels (w : TraceWord α V l) : Finset V :=
  usedLabels (fun i ↦ (w.blocks.block i).vertices)

omit [Fintype J] in
lemma exists_labelAt (hv : ∀ j, (α j).additionalVertices ≤ v)
    (w : TraceWord α V l) (u : w.labels) : ∃ s : TraceBlocks.Name l v, w.labelAt s = some u.val := by
  obtain ⟨i,hi⟩ := (mem_filter.mp u.property).2
  obtain ⟨p,hp⟩ := ((w.blocks.block i).mem_vertices_iff u.val).mp (mem_filter.mp hi).2
  have hBound := hv (w.val i).1
  let q : Fin (v+2) := ⟨p.val,p.isLt.trans_le (Nat.add_le_add_right hBound 2)⟩
  refine ⟨TraceBlocks.slot i q,?_⟩
  rw [labelAt,TraceBlocks.coordinates_slot]
  exact TraceBlocks.fullLabel_eq_some_iff.mpr ⟨p,rfl,hp⟩

omit [Fintype J] in
lemma mem_labels_of_labelAt (w : TraceWord α V l) {s : TraceBlocks.Name l v} {u : V}
    (he : w.labelAt s = some u) : u ∈ w.labels :=
  mem_filter.mpr ⟨mem_univ _,⟨(TraceBlocks.coordinates s).1,
    mem_filter.mpr ⟨mem_univ _,TraceBlocks.fullLabel_mem_vertices he⟩⟩⟩

omit [Fintype J] [Fintype V] in
lemma labelAt_eq_none_iff (w : TraceWord α V l) (s : TraceBlocks.Name l v) :
    w.labelAt s = none ↔ (TraceBlocks.coordinates s).2.val ≥
      (α (w.val (TraceBlocks.coordinates s).1).1).additionalVertices+2 := by
  unfold labelAt TraceBlocks.fullLabel
  split_ifs with h
  · simp only [false_iff]
    exact not_le_of_gt h
  · exact iff_of_true rfl (Nat.le_of_not_gt h)

omit [Fintype J] [Fintype V] in
lemma shapeWord_eq {w z : TraceWord α V l} (h : w.pattern v = z.pattern v) (i : Fin (l+2)) :
    (w.val i).1 = (z.val i).1 := congrFun (congrArg Prod.fst h) i

omit [Fintype J] [Fintype V] in
lemma labelAt_eq_none_iff_of_pattern_eq {w z : TraceWord α V l} (h : w.pattern v = z.pattern v)
    (s : TraceBlocks.Name l v) : w.labelAt s = none ↔ z.labelAt s = none := by
  rw [labelAt_eq_none_iff,labelAt_eq_none_iff,shapeWord_eq h]

omit [Fintype J] [Fintype V] in
lemma labelAt_eq_iff_of_pattern_eq {w z : TraceWord α V l} (h : w.pattern v = z.pattern v)
    (s t : TraceBlocks.Name l v) : w.labelAt s = w.labelAt t ↔ z.labelAt s = z.labelAt t := by
  have he := congrFun (congrFun (congrArg Prod.snd h) s) t
  exact decide_eq_decide.mp he

omit [Fintype J] [Fintype V] in
private lemma eq_of_labelAt_eq (hv : ∀ j, (α j).additionalVertices ≤ v)
    {w z : TraceWord α V l} (hp : w.pattern v = z.pattern v)
    (he : ∀ s : TraceBlocks.Name l v, w.labelAt s = z.labelAt s) : w = z := by
  apply Subtype.ext
  funext i
  have hi := shapeWord_eq hp i
  generalize hf : w.val i = a at *
  generalize hg : z.val i = b at *
  change a.1 = b.1 at hi
  obtain ⟨j,f⟩ := a
  obtain ⟨k,g⟩ := b
  change j = k at hi
  subst k
  congr 1
  ext p
  have hP : p.val < v+2 := p.isLt.trans_le (Nat.add_le_add_right (hv j) 2)
  have hAt (x : TraceWord α V l) (e : Fin (α j).toShape.vertexCount ↪ V) (hx : x.val i = ⟨j,e⟩) :
      x.labelAt (TraceBlocks.slot i ⟨p.val,hP⟩) = some (e p) := by
    rw [labelAt,TraceBlocks.coordinates_slot,TraceBlocks.fullLabel_eq_some_iff]
    have hX : (x.blocks.block i) = ⟨α j,e⟩ := congrArg BasicLabeling.block hx
    rw [hX]
    exact ⟨p,rfl,rfl⟩
  exact Option.some.inj ((hAt w f hf).symm.trans ((he _).trans (hAt z g hg)))

/-- Every word with this pattern is determined by an assignment to the distinct labels. -/
theorem card_fiber_pattern_le [Nonempty V] (hv : ∀ j, (α j).additionalVertices ≤ v)
    (w : TraceWord α V l) :
    ((univ : Finset (TraceWord α V l)).filter (fun z ↦ z.pattern v = w.pattern v)).card ≤
      Fintype.card V ^ w.labels.card := by
  let pos (u : w.labels) := (w.exists_labelAt hv u).choose
  have hPos (u : w.labels) : w.labelAt (pos u) = some u.val := (w.exists_labelAt hv u).choose_spec
  let assignment (z : TraceWord α V l) (u : w.labels) : V := (z.labelAt (pos u)).getD (Classical.arbitrary V)
  let fiber := (univ : Finset (TraceWord α V l)).filter (fun z ↦ z.pattern v = w.pattern v)
  have hInj : Set.InjOn assignment (↑fiber : Set (TraceWord α V l)) := by
    intro x hx y hy hxy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    apply eq_of_labelAt_eq hv (hx'.trans hy'.symm)
    intro s
    cases hs : w.labelAt s with
    | none =>
      exact ((labelAt_eq_none_iff_of_pattern_eq hx' s).mpr hs).trans
        ((labelAt_eq_none_iff_of_pattern_eq hy' s).mpr hs).symm
    | some a =>
      let u : w.labels := ⟨a,w.mem_labels_of_labelAt hs⟩
      have hEq : w.labelAt s = w.labelAt (pos u) := hs.trans (hPos u).symm
      rw [(labelAt_eq_iff_of_pattern_eq hx' s (pos u)).mpr hEq,
        (labelAt_eq_iff_of_pattern_eq hy' s (pos u)).mpr hEq]
      have hNone : w.labelAt (pos u) ≠ none := by rw [hPos]; exact Option.some_ne_none _
      have hX := hNone ∘ (labelAt_eq_none_iff_of_pattern_eq hx' (pos u)).mp
      have hY := hNone ∘ (labelAt_eq_none_iff_of_pattern_eq hy' (pos u)).mp
      have h := congrFun hxy u
      unfold assignment at h
      cases h₁ : x.labelAt (pos u) <;> cases h₂ : y.labelAt (pos u)
      · exact (hX h₁).elim
      · exact (hX h₁).elim
      · exact (hY h₂).elim
      · simpa only [h₁,h₂,Option.getD_some,Option.some.injEq] using h
  have h := card_le_card_of_injOn assignment (t := univ) (fun _ _ ↦ mem_univ _) hInj
  simpa only [card_univ,Fintype.card_fun,Fintype.card_coe] using h

omit [Fintype J] [Fintype V] in
/-- The code together with the forward shapes determines the shape word and label equalities. -/
theorem pattern_eq_of_code_eq (hα : Function.Injective α) (hv : ∀ j, (α j).additionalVertices ≤ v)
    {w z : TraceWord α V l}
    (hCode : ∀ i, TraceBlocks.encodeStep w.blocks v i = TraceBlocks.encodeStep z.blocks v i)
    (hF : ∀ i j, w.blocks.privatePair i j → (w.val i).1 = (z.val i).1) :
    w.pattern v = z.pattern v := by
  have hForward i j h := congrArg α (hF i j h)
  have hShape i := TraceBlocks.shape_eq_of_code_eq w.repeated z.repeated hCode hForward i
  have hSizes i := hv (w.val i).1
  apply Prod.ext
  · exact funext fun i ↦ hα (hShape i)
  · funext s t
    apply decide_eq_decide.mpr
    have hMask (q : TraceBlocks.Name l v) : w.labelAt q = none ↔ z.labelAt q = none := by
      rw [labelAt_eq_none_iff,labelAt_eq_none_iff,hα (hShape _)]
    cases hW₁ : w.labelAt s with
    | none =>
      rw [(hMask s).mp hW₁]
      exact ⟨fun h ↦ ((hMask t).mp h.symm).symm,fun h ↦ ((hMask t).mpr h.symm).symm⟩
    | some a =>
      cases hW₂ : w.labelAt t with
      | none =>
        rw [(hMask t).mp hW₂]
        exact iff_of_false (Option.some_ne_none _) (fun he ↦ Option.some_ne_none _ (hW₁.symm.trans ((hMask s).mpr he)))
      | some b =>
        cases hZ₁ : z.labelAt s with
        | none => exact (Option.some_ne_none _ ((hW₁.symm.trans ((hMask s).mpr hZ₁)))).elim
        | some a' =>
          cases hZ₂ : z.labelAt t with
          | none => exact (Option.some_ne_none _ ((hW₂.symm.trans ((hMask t).mpr hZ₂)))).elim
          | some b' =>
            simp only [Option.some.injEq]
            exact TraceBlocks.labels_eq_iff_of_code_eq w.repeated z.repeated hCode hForward hSizes
              hW₁ hZ₁ hW₂ hZ₂

end TraceWord

end LovaszTheta.Independent
