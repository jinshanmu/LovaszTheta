module

public import LovaszTheta.ChainProduct
public import LovaszTheta.CycleChange

/-!
# The backtracking identification

For fixed ordered boundaries, the spanning cycle fixes the
labeling of a basic shape. Identifying the last block edge for
edge and choosing its left endpoint as the destination is exactly
multiplication by its reversed shape.
-/

@[expose] public section

open SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

namespace LabeledBlock

/-- Two labelings of the same graph with the same ordered boundaries
have the same basic shape and vertex numbering. -/
theorem eq_of_graph_eq_of_boundaries {V : Type*} {b c : LabeledBlock V}
    (hG : b.graph = c.graph) (hL : b.left = c.left) (hR : b.right = c.right) : b = c := by
  have hS := additionalVertices_eq_of_graph_eq hG
  obtain ⟨⟨n,G,hG₀,hN₀⟩,f⟩ := b
  obtain ⟨⟨m,H,hH₀,hM₀⟩,g⟩ := c
  change n = m at hS
  subst m
  let b : LabeledBlock V := ⟨⟨n,G,hG₀,hN₀⟩,f⟩
  let c : LabeledBlock V := ⟨⟨n,H,hH₀,hM₀⟩,g⟩
  let e := pairedCyclePermutation b c hG
  have h₀ : e 0 = 0 := f.injective ((label_pairedCyclePermutation_left b c hG).trans hL.symm)
  have h₁ : e 1 = 1 := f.injective ((label_pairedCyclePermutation_right b c hG).trans hR.symm)
  have he : e = Equiv.refl (Fin (n+2)) := by
    calc
      e = cycleFrame (e 0) (e 1) := pairedCyclePermutation_eq_frame b c hG
      _ = Equiv.refl _ := by
        rw [h₀,h₁]
        ext i
        simp [cycleFrame,Equiv.addRight]
  have hGraph : G = H := by
    ext i j
    have hp := pairedCyclePermutation_adj_iff b c hG i j
    change G.Adj (e i) (e j) ↔ H.Adj i j at hp
    rw [he] at hp
    exact hp
  have hLabels : f = g := by
    apply Function.Embedding.ext
    intro j
    have hp := label_pairedCyclePermutation_apply b c hG j
    change f (e j) = g j at hp
    rw [he] at hp
    exact hp
  subst H
  subst g
  rfl

/-- With the starting boundary fixed, the destination is a cycle neighbor. -/
theorem right_eq_cycle_neighbor {V : Type*} {b c : LabeledBlock V}
    (hG : b.graph = c.graph) (hL : c.left = b.left) :
    c.right = b.right ∨ c.right = b.label (-1) := by
  let e := pairedCyclePermutation b c hG
  have h₀ : e 0 = 0 := b.label.injective ((label_pairedCyclePermutation_left b c hG).trans hL)
  have hEdge : (cycleGraph (b.shape.additionalVertices+2)).Adj
      (0 : Fin (b.shape.additionalVertices+2)) 1 := cycleGraph_adj.mpr (Or.inr (sub_zero 1))
  have hCycle := (cycleFrame_adj_iff (e 0) (e 1) 0 1).mpr hEdge
  have hFrame : e = cycleFrame (e 0) (e 1) := pairedCyclePermutation_eq_frame b c hG
  rw [← hFrame,h₀,cycleGraph_adj,zero_sub,sub_zero] at hCycle
  have hR : b.label (e 1) = c.right := label_pairedCyclePermutation_right b c hG
  rcases hCycle with he | he
  · have he' : e 1 = -1 := by simpa only [neg_neg] using congrArg Neg.neg he
    exact Or.inr (hR.symm.trans (congrArg b.label he'))
  · exact Or.inl (hR.symm.trans (congrArg b.label he))

lemma label_eq_of_eq_at_position {V : Type*} {b c : LabeledBlock V} (he : b = c)
    (u : Fin (b.shape.additionalVertices+2)) (v : Fin (c.shape.additionalVertices+2))
    (hv : u.val = v.val) : b.label u = c.label v := by
  subst c
  exact congrArg b.label (Fin.ext hv)

end LabeledBlock

namespace ChainTerm

variable (P : ChainTerm) (T : BasicShape)

/-- The final block, numbered from the outer right boundary back to the junction. -/
def reversedLast : LabeledBlock (Fin (P.append T).toShape.vertexCount) :=
  ⟨T.reverse,T.reverseIsomorphism.graphIso.toEquiv.toEmbedding.trans (P.appendedBlockEmb T)⟩

lemma reversedLast_left : (P.reversedLast T).left = (P.append T).toShape.right := by
  change P.appendedBlockEmb T (T.reverseIsomorphism.graphIso T.reverse.toShape.left) = _
  rw [T.reverseIsomorphism.map_left]
  exact P.appendedBlockEmb_right T

lemma reversedLast_right : (P.reversedLast T).right = P.tailEmb T 0 := by
  change P.appendedBlockEmb T (T.reverseIsomorphism.graphIso T.reverse.toShape.right) = _
  rw [T.reverseIsomorphism.map_right]
  apply Fin.ext
  change P.span + (-(0 : Fin (T.span+1))).val = P.span+0
  simp only [neg_zero,Fin.val_zero]

lemma reversedLast_graph : (P.reversedLast T).graph = T.pathGraph.map (P.tailEmb T) := by
  let e : Fin (T.reverse.additionalVertices+2) ≃ Fin (T.additionalVertices+2) :=
    T.reverseIsomorphism.graphIso.toEquiv
  let f : Fin (T.additionalVertices+2) ↪ Fin (P.append T).toShape.vertexCount := P.appendedBlockEmb T
  have hG : T.reverse.graph.map e.toEmbedding = T.graph := by
    ext a b
    obtain ⟨i,rfl⟩ := e.surjective a
    obtain ⟨j,rfl⟩ := e.surjective b
    exact SimpleGraph.map_adj_apply.trans (T.reverseIsomorphism.graphIso.map_adj_iff).symm
  have hF : T.graph.map f = T.pathGraph.map (P.tailEmb T) := by
    change T.graph.map ((P.tailEmb T) ∘ (Equiv.neg (Fin (T.span+1))).toEmbedding) = _
    rw [← SimpleGraph.map_map]
    congr 1
    exact (SimpleGraph.comap_symm T.graph (Equiv.neg (Fin (T.span+1)))).symm
  calc
    _ = (T.reverse.graph.map e.toEmbedding).map f := by
      rw [SimpleGraph.map_map]
      rfl
    _ = _ := by rw [hG]; exact hF

variable (S : BasicShape) (p : Identification (P.append T).toShape S.toShape)

/-- The multiplying block placed in the old vertex coordinates in an exact cancellation. -/
noncomputable def cancellationBlock (h : p.newGraph = P.lastGraph T S p) :
    LabeledBlock (Fin (P.append T).toShape.vertexCount) :=
  ⟨S,p.containedEmbedding (h.le.trans (P.lastGraph_le_oldGraph T S p)) S.incident⟩

lemma cancellationBlock_label (h : p.newGraph = P.lastGraph T S p) (i : Fin S.toShape.vertexCount) :
    p.old ((P.cancellationBlock T S p h).label i) = p.new i :=
  p.old_containedEmbedding (h.le.trans (P.lastGraph_le_oldGraph T S p)) S.incident i

lemma cancellationBlock_graph (h : p.newGraph = P.lastGraph T S p) :
    (P.cancellationBlock T S p h).graph = T.pathGraph.map (P.tailEmb T) := by
  have h₁ : ((P.cancellationBlock T S p h).graph).map p.old = p.newGraph := by
    let e : Fin (S.additionalVertices+2) ↪ Fin (P.append T).toShape.vertexCount :=
      (P.cancellationBlock T S p h).label
    change (S.graph.map e).map p.old = S.graph.map p.new
    rw [SimpleGraph.map_map]
    exact congrArg (fun f ↦ S.graph.map f) (funext (P.cancellationBlock_label T S p h))
  have h₂ : (T.pathGraph.map (P.tailEmb T)).map p.old = P.lastGraph T S p := by
    rw [SimpleGraph.map_map]
    rfl
  have he := congrArg (fun G ↦ G.comap p.old) (h₁.trans (h.trans h₂.symm))
  simpa only [SimpleGraph.comap_map_eq] using he

lemma cancellationBlock_left (h : p.newGraph = P.lastGraph T S p) :
    (P.cancellationBlock T S p h).left = (P.append T).toShape.right :=
  p.containedEmbedding_left (h.le.trans (P.lastGraph_le_oldGraph T S p)) S.incident

lemma cancellationBlock_right_of_backtrack (h : p.newGraph = P.lastGraph T S p)
    (hw : p.outputRight = P.junction T S p) :
    (P.cancellationBlock T S p h).right = P.tailEmb T 0 :=
  p.old.injective ((P.cancellationBlock_label T S p h S.toShape.right).trans hw)

/-- Returning to the junction with exact edge cancellation forces the reversed block. -/
theorem cancellationBlock_eq_reversedLast (h : p.newGraph = P.lastGraph T S p)
    (hw : p.outputRight = P.junction T S p) :
    P.cancellationBlock T S p h = P.reversedLast T :=
  LabeledBlock.eq_of_graph_eq_of_boundaries
    ((P.cancellationBlock_graph T S p h).trans (P.reversedLast_graph T).symm)
    ((P.cancellationBlock_left T S p h).trans (P.reversedLast_left T).symm)
    ((P.cancellationBlock_right_of_backtrack T S p h hw).trans (P.reversedLast_right T).symm)

lemma eq_reverse_of_backtrack (h : p.newGraph = P.lastGraph T S p)
    (hw : p.outputRight = P.junction T S p) : S = T.reverse :=
  congrArg LabeledBlock.shape (P.cancellationBlock_eq_reversedLast T S p h hw)

/-- The identification of the reversed block with the final block. -/
def backtrackIdentification :
    Identification (P.append T).toShape T.reverse.toShape :=
  ⟨fun j ↦ some ((P.reversedLast T).label j),congrArg some (P.reversedLast_left T),
    fun _ _ _ h₁ h₂ ↦ (P.reversedLast T).label.injective
      ((Option.some.inj h₁).trans (Option.some.inj h₂).symm)⟩

lemma backtrack_newGraph :
    (P.backtrackIdentification T).newGraph = P.lastGraph T T.reverse (P.backtrackIdentification T) := by
  let p := P.backtrackIdentification T
  let e : Fin (T.reverse.additionalVertices+2) ↪ Fin (P.append T).toShape.vertexCount :=
    (P.reversedLast T).label
  have hE : (p.new : Fin (T.reverse.additionalVertices+2) → p.Vertex) = p.old ∘ e :=
    funext fun i ↦ p.new_of_some (j := i) rfl
  have hG : T.reverse.graph.map e = T.pathGraph.map (P.tailEmb T) := P.reversedLast_graph T
  change T.reverse.graph.map p.new = P.lastGraph T T.reverse p
  calc
    _ = T.reverse.graph.map (p.old ∘ e) := congrArg (fun f ↦ T.reverse.graph.map f) hE
    _ = (T.reverse.graph.map e).map p.old := (SimpleGraph.map_map T.reverse.graph _ _).symm
    _ = _ := by rw [hG,SimpleGraph.map_map]; rfl

lemma backtrack_right :
    (P.backtrackIdentification T).outputRight = P.junction T T.reverse (P.backtrackIdentification T) := by
  let p := P.backtrackIdentification T
  change p.new T.reverse.toShape.right = p.old (P.tailEmb T 0)
  exact (p.new_of_some (j := T.reverse.toShape.right) (i := (P.reversedLast T).right) rfl).trans
    (congrArg p.old (P.reversedLast_right T))

lemma backtrack_ne_fresh :
    P.backtrackIdentification T ≠ Identification.fresh (P.append T).toShape T.reverse.toShape := by
  intro h
  have hN : T.reverse.toShape.right ≠ T.reverse.toShape.left := (P.reversedLast T).left_ne_right.symm ∘
    congrArg (P.reversedLast T).label
  have he := congrArg (fun q : Identification (P.append T).toShape T.reverse.toShape ↦ q.val T.reverse.toShape.right) h
  change some ((P.reversedLast T).label T.reverse.toShape.right) =
    if T.reverse.toShape.right = T.reverse.toShape.left then some (P.append T).toShape.right else none at he
  rw [ite_eq_right hN] at he
  cases he

/-- At the backtracking destination there is just one identification. -/
theorem eq_backtrackIdentification
    (p : Identification (P.append T).toShape T.reverse.toShape)
    (h : p.newGraph = P.lastGraph T T.reverse p) (hw : p.outputRight = P.junction T T.reverse p) :
    p = P.backtrackIdentification T := by
  apply Subtype.ext
  funext j
  change p.val j = some ((P.reversedLast T).label j)
  apply p.overlap_iff.mp
  have he := P.cancellationBlock_label T T.reverse p h j
  have hLabels := LabeledBlock.label_eq_of_eq_at_position
    (P.cancellationBlock_eq_reversedLast T T.reverse p h hw) j j rfl
  exact he.symm.trans (congrArg p.old hLabels)

/-- Exact cancellation leaves a right boundary at a cycle neighbor of the old right endpoint. -/
theorem exact_right_eq_junction_or_neighbor (h : p.newGraph = P.lastGraph T S p) :
    p.outputRight = P.junction T S p ∨ p.outputRight = p.old ((P.reversedLast T).label (-1)) := by
  have hG := (P.reversedLast_graph T).trans (P.cancellationBlock_graph T S p h).symm
  have hL := (P.cancellationBlock_left T S p h).trans (P.reversedLast_left T).symm
  have hR : p.old ((P.cancellationBlock T S p h).right) = p.outputRight :=
    P.cancellationBlock_label T S p h S.toShape.right
  rcases LabeledBlock.right_eq_cycle_neighbor hG hL with he | he
  · exact Or.inl (hR.symm.trans (congrArg p.old (he.trans (P.reversedLast_right T))))
  · exact Or.inr (hR.symm.trans (congrArg p.old he))

/-- At a fixed destination, exact cancellation permits at most one identification. -/
theorem exact_identification_unique (q : Identification (P.append T).toShape S.toShape)
    (hp : p.newGraph = P.lastGraph T S p) (hq : q.newGraph = P.lastGraph T S q)
    (hRight : (P.cancellationBlock T S p hp).right = (P.cancellationBlock T S q hq).right) : p = q := by
  have hBlocks := LabeledBlock.eq_of_graph_eq_of_boundaries
    ((P.cancellationBlock_graph T S p hp).trans (P.cancellationBlock_graph T S q hq).symm)
    ((P.cancellationBlock_left T S p hp).trans (P.cancellationBlock_left T S q hq).symm) hRight
  apply Subtype.ext
  funext i
  have h₁ := p.overlap_iff.mp (P.cancellationBlock_label T S p hp i).symm
  have h₂ := q.overlap_iff.mp (P.cancellationBlock_label T S q hq i).symm
  rw [h₁,h₂,LabeledBlock.label_eq_of_eq_at_position hBlocks i i rfl]

end ChainTerm

end LovaszTheta.Independent
