module

public import LovaszTheta.LabeledBlocks
public import LovaszTheta.CycleFrames

/-!
# Coordinates of an edge-for-edge pair

Equal labeled graphs have equal label ranges. The resulting
permutation between the cycle coordinates is fixed by the two
return boundaries.
-/

@[expose] public section

open Finset SimpleGraph

namespace LovaszTheta.Independent.LabeledBlock

variable {V : Type*}

/-- The vertex count of a labeled block is the vertex count of its basic shape. -/
lemma card_vertices (b : LabeledBlock V) : b.vertices.card = b.shape.additionalVertices+2 := by
  simp only [vertices,card_map,card_univ,Fintype.card_fin]

lemma additionalVertices_eq_of_graph_eq {b c : LabeledBlock V} (h : b.graph = c.graph) :
    b.shape.additionalVertices = c.shape.additionalVertices := by
  have he := congrArg Finset.card (vertices_eq_of_graph_eq h)
  rw [card_vertices,card_vertices] at he
  exact Nat.add_right_cancel he

/-- The change of coordinates determined by the equal ranges of two labelings. -/
noncomputable def changeCoordinates (b c : LabeledBlock V) (h : b.graph = c.graph) :
    Fin (c.shape.additionalVertices+2) ≃ Fin (b.shape.additionalVertices+2) :=
  let hRange : Set.range c.label = Set.range b.label := Set.ext fun v ↦
    ((c.mem_vertices_iff v).symm.trans (by rw [vertices_eq_of_graph_eq h])).trans (b.mem_vertices_iff v)
  (Equiv.ofInjective c.label c.label.injective).trans ((Set.equivOfEq hRange).trans
    (Equiv.ofInjective b.label b.label.injective).symm)

lemma label_changeCoordinates (b c : LabeledBlock V) (h : b.graph = c.graph)
    (i : Fin (c.shape.additionalVertices+2)) :
    b.label (changeCoordinates b c h i) = c.label i := by
  unfold changeCoordinates
  dsimp only [Equiv.trans_apply]
  let E := Equiv.ofInjective b.label b.label.injective
  exact congrArg Subtype.val (E.apply_symm_apply _)

lemma adj_changeCoordinates_iff (b c : LabeledBlock V) (h : b.graph = c.graph)
    (i j : Fin (c.shape.additionalVertices+2)) :
    b.shape.graph.Adj (changeCoordinates b c h i) (changeCoordinates b c h j) ↔ c.shape.graph.Adj i j := by
  rw [← b.graph_adj_label,label_changeCoordinates,label_changeCoordinates,h,c.graph_adj_label]

/-- The index transport for the common cycle size, followed by the labeling permutation. -/
noncomputable def pairedCyclePermutation (b c : LabeledBlock V) (h : b.graph = c.graph) :
    Equiv.Perm (Fin (b.shape.additionalVertices+2)) :=
  (finCongr (congrArg (· + 2) (additionalVertices_eq_of_graph_eq h))).trans (changeCoordinates b c h)

private lemma adj_finCongr {n m : ℕ} (h : n = m) {i j : Fin (n+2)}
    (hA : (cycleGraph (n+2)).Adj i j) :
    (cycleGraph (m+2)).Adj (finCongr (congrArg (·+2) h) i) (finCongr (congrArg (·+2) h) j) := by
  subst m
  exact hA

/-- Equal labeled blocks differ by the rotation or reflection specified by the return endpoints. -/
theorem pairedCyclePermutation_eq_frame (b c : LabeledBlock V) (h : b.graph = c.graph) :
    pairedCyclePermutation b c h =
      cycleFrame (pairedCyclePermutation b c h 0) (pairedCyclePermutation b c h 1) := by
  let e := pairedCyclePermutation b c h
  apply cyclePermutation_eq_cycleFrame e
  intro i j hi
  have hE {i j : Fin (b.shape.additionalVertices+2)} (hA : (cycleGraph (b.shape.additionalVertices+2)).Adj i j) :
      b.shape.graph.Adj (e i) (e j) := by
    apply (adj_changeCoordinates_iff b c h _ _).mpr
    exact c.shape.cycle_le (adj_finCongr (additionalVertices_eq_of_graph_eq h) hA)
  exact cycle_adj_of_spanning_cycle b.shape.noncrossing e hE hi

/-- The common-size return graph is the forward graph pulled back by its return orientation. -/
theorem pairedCyclePermutation_adj_iff (b c : LabeledBlock V) (h : b.graph = c.graph)
    (i j : Fin (b.shape.additionalVertices+2)) :
    b.shape.graph.Adj (pairedCyclePermutation b c h i) (pairedCyclePermutation b c h j) ↔
      c.shape.graph.Adj
        (finCongr (congrArg (·+2) (additionalVertices_eq_of_graph_eq h)) i)
        (finCongr (congrArg (·+2) (additionalVertices_eq_of_graph_eq h)) j) :=
  adj_changeCoordinates_iff b c h _ _

end LovaszTheta.Independent.LabeledBlock
