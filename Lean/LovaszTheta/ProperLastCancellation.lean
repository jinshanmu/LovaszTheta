module

public import LovaszTheta.LastBlockCancellation

/-!
# Proper cancellation inside the last block

When the second block cancels in full but covers a proper subset of
the last block's edges, split that last block into its surviving and
canceled edges. The same two-mixed-vertex argument applies.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

namespace BasicShape

lemma cycle_le_pathGraph (T : BasicShape) : cycleGraph (T.additionalVertices+2) ≤ T.pathGraph := by
  intro a b h
  apply T.cycle_le
  rw [cycleGraph_adj,show -a- -b = b-a by abel,show -b- -a = a-b by abel,or_comm]
  exact cycleGraph_adj.mp h

lemma incident_pathGraph (T : BasicShape) (u : Fin (T.span+1)) : Incident T.pathGraph u :=
  ⟨u+1,T.cycle_le_pathGraph (cycleGraph_adj.mpr (Or.inr (by abel)))⟩

lemma vertexDeletionConnected_pathGraph (T : BasicShape) : VertexDeletionConnected T.pathGraph := by
  intro x
  exact (vertexDeletionConnected_cycleGraph T.additionalVertices x).mono
    (fun _ _ h ↦ T.cycle_le_pathGraph h)

end BasicShape

namespace ChainTerm

variable (P : ChainTerm) (T S : BasicShape)
variable (p : Identification (P.append T).toShape S.toShape)

/-- The last block in the quotient. -/
def lastGraph : SimpleGraph p.Vertex := T.pathGraph.map (P.lastInQuotient T S p)

lemma lastGraph_le_oldGraph : P.lastGraph T S p ≤ p.oldGraph := by
  rw [P.oldGraph_eq_prefix_sup_last T S p]
  exact le_sup_right

/-- The edges of the old last block left after cancellation. -/
def lastSurvives : SimpleGraph (Fin (T.span+1)) :=
  T.pathGraph \ p.newGraph.comap (P.lastInQuotient T S p)

/-- The canceled edges of the old last block. -/
def lastCancels : SimpleGraph (Fin (T.span+1)) :=
  T.pathGraph ⊓ p.newGraph.comap (P.lastInQuotient T S p)

lemma last_partition {a b : Fin (T.span+1)} (h : T.pathGraph.Adj a b) :
    (P.lastSurvives T S p).Adj a b ∨ (P.lastCancels T S p).Adj a b := by
  by_cases he : p.newGraph.Adj (P.lastInQuotient T S p a) (P.lastInQuotient T S p b)
  · exact Or.inr ⟨h,he⟩
  · exact Or.inl ⟨h,he⟩

lemma lastSurvives_map_le :
    (P.lastSurvives T S p).map (P.lastInQuotient T S p) ≤ p.remaining := by
  intro u w h
  obtain ⟨a,b,he,rfl,rfl⟩ := (SimpleGraph.map_adj (P.lastInQuotient T S p) _ _ _).mp h
  exact Or.inl ⟨P.lastGraph_le_oldGraph T S p (SimpleGraph.map_adj_apply.mpr he.1),he.2⟩

lemma old_of_last_mixed (a : Fin (T.span+1)) (h : Mixed (P.lastSurvives T S p) (P.lastCancels T S p) a) :
    P.lastInQuotient T S p a ∈ p.liveShared := by
  obtain ⟨b,hb⟩ := h.1
  obtain ⟨c,hc⟩ := h.2
  exact p.mem_liveShared.mpr ⟨p.mem_shared.mpr
    ⟨⟨_,rfl⟩,p.mem_new_of_newAdj hc.2⟩,
    Or.inl ⟨_,P.lastSurvives_map_le T S p (SimpleGraph.map_adj_apply.mpr hb)⟩⟩

lemma new_range_subset_last_range (h : p.newGraph ≤ P.lastGraph T S p) :
    Set.range p.new ⊆ Set.range (P.lastInQuotient T S p) := by
  rintro _ ⟨a,rfl⟩
  obtain ⟨b,hb⟩ := S.incident a
  obtain ⟨u,v,he,hu,hv⟩ := (SimpleGraph.map_adj (P.lastInQuotient T S p) _ _ _).mp
    (h (SimpleGraph.map_adj_apply.mpr hb))
  exact ⟨u,hu⟩

/-- Complete but proper cancellation in the last block has two live shared
vertices, and forces boundary connectivity when a single chain has just two. -/
theorem partial_last_cancellation (h : p.newGraph ≤ P.lastGraph T S p)
    (hne : p.newGraph ≠ P.lastGraph T S p) :
    2 ≤ p.liveShared.card ∧
      (p.liveShared.card ≤ 2 → (P.append T).graph.Reachable (P.append T).toShape.left (P.append T).toShape.right →
        p.remaining.Reachable p.outputLeft p.outputRight) := by
  have hB : ∃ a, Incident (P.lastCancels T S p) a := by
    obtain ⟨j,hj⟩ := S.incident S.toShape.left
    have hN : p.newGraph.Adj (p.new S.toShape.left) (p.new j) := SimpleGraph.map_adj_apply.mpr hj
    obtain ⟨a,b,hAB,ha,hb⟩ := (SimpleGraph.map_adj (P.lastInQuotient T S p) _ _ _).mp (h hN)
    refine ⟨a,b,hAB,?_⟩
    change p.newGraph.Adj (P.lastInQuotient T S p a) (P.lastInQuotient T S p b)
    rwa [ha,hb]
  have hR : ∃ a, Incident (P.lastSurvives T S p) a := by
    by_contra hR
    apply hne
    apply le_antisymm h
    intro u v he
    obtain ⟨a,b,hAB,rfl,rfl⟩ := (SimpleGraph.map_adj (P.lastInQuotient T S p) _ _ _).mp he
    rcases P.last_partition T S p hAB with hR' | hB'
    · exact (hR ⟨a,b,hR'⟩).elim
    · exact hB'.2
  refine ⟨p.two_le_liveShared_of_split (P.lastInQuotient T S p) T.vertexDeletionConnected_pathGraph
    (fun h' ↦ P.last_partition T S p h') hR hB (P.old_of_last_mixed T S p),?_⟩
  intro hCard hPath
  obtain ⟨u,hu,hU⟩ := p.reachable_liveShared hPath
  obtain ⟨r,hr⟩ := P.new_range_subset_last_range T S p h (Set.mem_range_self S.toShape.right)
  have hRight : p.outputRight ∈ p.liveShared :=
    p.mem_liveShared.mpr ⟨p.mem_shared.mpr ⟨⟨_,hr⟩,⟨_,rfl⟩⟩,Or.inr (Or.inr rfl)⟩
  exact hU.trans (p.reachable_right_of_split (P.lastInQuotient T S p) T.vertexDeletionConnected_pathGraph
    (fun hx ↦ P.last_partition T S p hx) hR hB (P.old_of_last_mixed T S p)
    (P.lastSurvives_map_le T S p) ⟨r,hr,Or.inr hRight⟩ hCard hu)

end ChainTerm

end LovaszTheta.Independent
