module

public import LovaszTheta.BasicShapeRigidity
public import LovaszTheta.EdgeSplit

/-!
# Injectively labeled basic blocks

The labeled edges recover all labels of a block. A split by
membership in a second graph has two mixed labels as soon as
both parts are nonempty.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

/-- A basic shape with injective labels in an ambient vertex type. -/
structure LabeledBlock (V : Type*) where
  /-- The basic shape in canonical cycle coordinates. -/
  shape : BasicShape
  /-- The injective labeling. -/
  label : Fin (shape.additionalVertices+2) ↪ V

namespace LabeledBlock

variable {V : Type*}

/-- Left boundary label. -/
def left (b : LabeledBlock V) : V := b.label 0

/-- Right boundary label. -/
def right (b : LabeledBlock V) : V := b.label 1

/-- All labels in the block. -/
noncomputable def vertices (b : LabeledBlock V) : Finset V :=
  univ.map b.label

/-- The graph of labeled edges, with the unused labels isolated. -/
def graph (b : LabeledBlock V) : SimpleGraph V :=
  b.shape.graph.map b.label

lemma mem_vertices_iff (b : LabeledBlock V) (v : V) :
    v ∈ b.vertices ↔ ∃ a, b.label a = v := by
  simp only [vertices,mem_map,mem_univ,true_and]

lemma left_mem_vertices (b : LabeledBlock V) : b.left ∈ b.vertices :=
  (b.mem_vertices_iff _).mpr ⟨0,rfl⟩

lemma right_mem_vertices (b : LabeledBlock V) : b.right ∈ b.vertices :=
  (b.mem_vertices_iff _).mpr ⟨1,rfl⟩

lemma left_ne_right (b : LabeledBlock V) : b.left ≠ b.right :=
  b.label.injective.ne (by simp)

lemma graph_adj_label (b : LabeledBlock V) {u v : Fin (b.shape.additionalVertices+2)} :
    b.graph.Adj (b.label u) (b.label v) ↔ b.shape.graph.Adj u v :=
  SimpleGraph.map_adj_apply

lemma graph_adj_left_right (b : LabeledBlock V) : b.graph.Adj b.left b.right :=
  b.graph_adj_label.mpr b.shape.toShape_left_adj_right

lemma incident_iff_mem_vertices (b : LabeledBlock V) (v : V) : Incident b.graph v ↔ v ∈ b.vertices := by
  rw [b.mem_vertices_iff v]
  constructor
  · rintro ⟨w,h⟩
    obtain ⟨a,_,_,he,_⟩ := (SimpleGraph.map_adj b.label b.shape.graph v w).mp h
    exact ⟨a,he⟩
  · rintro ⟨a,rfl⟩
    refine ⟨b.label (a+1),b.graph_adj_label.mpr (b.shape.cycle_le (cycleGraph_adj.mpr (Or.inr ?_)))⟩
    rw [add_comm a,add_sub_cancel_right]

lemma mem_vertices_of_adj {b : LabeledBlock V} {u v : V} (h : b.graph.Adj u v) :
    u ∈ b.vertices :=
  (b.incident_iff_mem_vertices _).mp ⟨_,h⟩

lemma vertices_eq_of_graph_eq {b c : LabeledBlock V} (h : b.graph = c.graph) : b.vertices = c.vertices := by
  ext a
  rw [← b.incident_iff_mem_vertices,← c.incident_iff_mem_vertices,h]

/-- Propagation of a predicate along the vertex-deleted block. -/
theorem prop_of_vertexDeletion {b : LabeledBlock V} {d u v : V} (hd : d ∈ b.vertices)
    (hu : u ∈ b.vertices) (hv : v ∈ b.vertices) (hud : u ≠ d) (hvd : v ≠ d)
    {P : V → Prop} (hE : ∀ {a c : V}, b.graph.Adj a c → a ≠ d → c ≠ d → P a → P c) (huP : P u) : P v := by
  obtain ⟨j,rfl⟩ := (b.mem_vertices_iff _).mp hd
  obtain ⟨i,rfl⟩ := (b.mem_vertices_iff _).mp hu
  obtain ⟨k,rfl⟩ := (b.mem_vertices_iff _).mp hv
  let p : {a : Fin (b.shape.additionalVertices+2) // a ≠ j} := ⟨i,fun h ↦ hud (congrArg b.label h)⟩
  let q : {a : Fin (b.shape.additionalVertices+2) // a ≠ j} := ⟨k,fun h ↦ hvd (congrArg b.label h)⟩
  have hP {w : {a : Fin (b.shape.additionalVertices+2) // a ≠ j}}
      (hPath : Relation.ReflTransGen (b.shape.graph.induce {a | a ≠ j}).Adj p w) : P (b.label w.val) := by
    induction hPath with
    | refl => exact huP
    | tail _hPrev hAdj ih =>
      rename_i a c
      exact hE (b.graph_adj_label.mpr hAdj) (b.label.injective.ne a.property)
        (b.label.injective.ne c.property) ih
  have h := b.shape.vertexDeletionConnected j p q
  rw [reachable_iff_reflTransGen] at h
  exact hP h

/-- Two mixed labels for a partial edge overlap with a second graph. -/
theorem exists_two_mixed_of_partial_overlap (b : LabeledBlock V) (G : SimpleGraph V)
    (hR : ∃ u v, b.graph.Adj u v ∧ G.Adj u v)
    (hB : ∃ u v, b.graph.Adj u v ∧ ¬G.Adj u v) :
    ∃ u v : V, u ≠ v ∧ Mixed (b.graph ⊓ G) (b.graph \ G) u ∧ Mixed (b.graph ⊓ G) (b.graph \ G) v := by
  let R := b.shape.graph ⊓ G.comap b.label
  let B := b.shape.graph \ G.comap b.label
  have hPart {u v : Fin (b.shape.additionalVertices+2)} (h : b.shape.graph.Adj u v) :
      R.Adj u v ∨ B.Adj u v := by
    by_cases hg : G.Adj (b.label u) (b.label v)
    · exact Or.inl ⟨h,hg⟩
    · exact Or.inr ⟨h,hg⟩
  obtain ⟨u,v,huv,hg⟩ := hR
  obtain ⟨a,c,hac,rfl,rfl⟩ := (SimpleGraph.map_adj b.label b.shape.graph u v).mp huv
  obtain ⟨u',v',huv',hg'⟩ := hB
  obtain ⟨a',c',hac',rfl,rfl⟩ := (SimpleGraph.map_adj b.label b.shape.graph u' v').mp huv'
  obtain ⟨i,j,hij,_,_,hi,hj⟩ := exists_two_mixed_of_edgeSplit b.shape.vertexDeletionConnected
    @hPart (show Incident R a from ⟨c,hac,hg⟩) (show ∃ i, Incident B i from ⟨a',c',hac',hg'⟩)
  have hMap {k : Fin (b.shape.additionalVertices+2)} (hk : Mixed R B k) :
      Mixed (b.graph ⊓ G) (b.graph \ G) (b.label k) := by
    obtain ⟨⟨p,hp₁,hp₂⟩,⟨q,hq₁,hq₂⟩⟩ := hk
    exact ⟨⟨_,b.graph_adj_label.mpr hp₁,hp₂⟩,⟨_,b.graph_adj_label.mpr hq₁,hq₂⟩⟩
  exact ⟨b.label i,b.label j,b.label.injective.ne hij,hMap hi,hMap hj⟩

end LabeledBlock

end LovaszTheta.Independent
