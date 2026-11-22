module

public import LovaszTheta.SharedVertices

/-!
# Partial edge cancellation

A split inside a block forces two mixed vertices. If the quotient
retains only those two shared vertices, the surviving part of that
block connects both to the new right boundary.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent.Identification

variable {P S : Shape} (p : Identification P S)

omit p in
theorem exists_two_live_of_split {F : Type*} {G R B : SimpleGraph F}
    (hG : VertexDeletionConnected G) (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    (hR : ∃ a, Incident R a) (hB : ∃ b, Incident B b) :
    ∃ a b, a ≠ b ∧ Mixed R B a ∧ Mixed R B b := by
  obtain ⟨a,ha⟩ := hR
  obtain ⟨b,c,hn,_,_,hb,hc⟩ := exists_two_mixed_of_edgeSplit hG hPartition ha hB
  exact ⟨b,c,hn,hb,hc⟩

theorem two_le_liveShared_of_split {F : Type*} (e : F ↪ p.Vertex)
    {G R B : SimpleGraph F} (hG : VertexDeletionConnected G)
    (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    (hR : ∃ a, Incident R a) (hB : ∃ b, Incident B b)
    (hLive : ∀ u, Mixed R B u → e u ∈ p.liveShared) :
    2 ≤ p.liveShared.card := by
  obtain ⟨a,b,hn,ha,hb⟩ := exists_two_live_of_split hG hPartition hR hB
  have hSub : ({e a,e b} : Finset p.Vertex) ⊆ p.liveShared :=
    fun u hu ↦ by
      rcases mem_insert.mp hu with rfl | hu
      · exact hLive _ ha
      · rw [mem_singleton.mp hu]
        exact hLive _ hb
  exact (card_pair (e.injective.ne hn)).ge.trans (card_le_card hSub)

theorem reachable_right_of_split {F : Type*} [Fintype F] (e : F ↪ p.Vertex)
    {G R B : SimpleGraph F} (hG : VertexDeletionConnected G)
    (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    (hR : ∃ a, Incident R a) (hB : ∃ b, Incident B b)
    (hLive : ∀ u, Mixed R B u → e u ∈ p.liveShared) (hSub : R.map e ≤ p.remaining)
    (hRight : ∃ r, e r = p.outputRight ∧ (Incident R r ∨ p.outputRight ∈ p.liveShared))
    (hCard : p.liveShared.card ≤ 2) {u : p.Vertex} (hu : u ∈ p.liveShared) :
    p.remaining.Reachable u p.outputRight := by
  obtain ⟨a,b,hn,ha,hb⟩ := exists_two_live_of_split hG hPartition hR hB
  have hAB : ({e a,e b} : Finset p.Vertex) ⊆ p.liveShared := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hLive _ ha
    · exact hLive _ hb
  have hEq : ({e a,e b} : Finset p.Vertex) = p.liveShared :=
    eq_of_subset_of_card_le hAB (by rwa [card_pair (e.injective.ne hn)])
  have hExists (v : p.Vertex) (hv : v ∈ p.liveShared) : ∃ t, e t = v ∧ Incident R t := by
    rw [← hEq,mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨a,rfl,ha.1⟩
    · exact ⟨b,rfl,hb.1⟩
  obtain ⟨w,rfl,hw⟩ := hExists u hu
  obtain ⟨r,hr,hRr | hRr⟩ := hRight
  · have hMixed : (univ.filter (Mixed R B)).card ≤ 2 :=
      (card_le_card_of_injOn e (fun u hu ↦ hLive u (mem_filter.mp hu).2) e.injective.injOn).trans hCard
    have h := (reachable_of_edgeSplit_card_mixed_le_two hG hPartition hB hMixed hw hRr).map
      (SimpleGraph.Embedding.map e R).toHom
    rw [← hr]
    exact h.mono hSub
  · obtain ⟨r',hr',hr''⟩ := hExists _ hRr
    have hMixed : (univ.filter (Mixed R B)).card ≤ 2 :=
      (card_le_card_of_injOn e (fun u hu ↦ hLive u (mem_filter.mp hu).2) e.injective.injOn).trans hCard
    have h := (reachable_of_edgeSplit_card_mixed_le_two hG hPartition hB hMixed hw hr'').map
      (SimpleGraph.Embedding.map e R).toHom
    rw [← hr']
    exact h.mono hSub

/-- The edges of the multiplying block that survive in the product. -/
def newSurvives : SimpleGraph (Fin S.vertexCount) := S.graph \ p.oldGraph.comap p.new

/-- The edges of the multiplying block canceled by the old factor. -/
def newCancels : SimpleGraph (Fin S.vertexCount) := S.graph ⊓ p.oldGraph.comap p.new

lemma new_partition {a b : Fin S.vertexCount} (h : S.graph.Adj a b) :
    p.newSurvives.Adj a b ∨ p.newCancels.Adj a b := by
  by_cases he : p.oldGraph.Adj (p.new a) (p.new b)
  · exact Or.inr ⟨h,he⟩
  · exact Or.inl ⟨h,he⟩

lemma newSurvives_map_le : p.newSurvives.map p.new ≤ p.remaining := by
  intro u w h
  obtain ⟨a,b,he,rfl,rfl⟩ := (SimpleGraph.map_adj p.new p.newSurvives _ _).mp h
  exact Or.inr ⟨SimpleGraph.map_adj_apply.mpr he.1,he.2⟩

lemma liveShared_of_new_mixed (u : Fin S.vertexCount) (h : Mixed p.newSurvives p.newCancels u) :
    p.new u ∈ p.liveShared := by
  obtain ⟨v,hv⟩ := h.1
  obtain ⟨w,hw⟩ := h.2
  exact p.mem_liveShared.mpr ⟨p.mem_shared.mpr ⟨p.mem_old_of_oldAdj hw.2,⟨u,rfl⟩⟩,
    Or.inl ⟨_,p.newSurvives_map_le (SimpleGraph.map_adj_apply.mpr hv)⟩⟩

lemma right_incident_or_liveShared (h : Incident S.graph S.right) :
    Incident p.newSurvives S.right ∨ p.outputRight ∈ p.liveShared := by
  obtain ⟨u,hu⟩ := h
  rcases p.new_partition hu with hS | hC
  · exact Or.inl ⟨u,hS⟩
  · exact Or.inr (p.mem_liveShared.mpr ⟨p.mem_shared.mpr ⟨p.mem_old_of_oldAdj hC.2,⟨_,rfl⟩⟩,
      Or.inr (Or.inr rfl)⟩)

/-- Some but not all edges of the multiplying block cancel. -/
theorem partial_new_cancellation (hS : VertexDeletionConnected S.graph)
    (hIncident : Incident S.graph S.right)
    (hR : ∃ a, Incident p.newSurvives a) (hB : ∃ a, Incident p.newCancels a) :
    2 ≤ p.liveShared.card ∧
      (p.liveShared.card ≤ 2 → P.graph.Reachable P.left P.right →
        p.remaining.Reachable p.outputLeft p.outputRight) := by
  refine ⟨p.two_le_liveShared_of_split p.new hS (fun h ↦ p.new_partition h) hR hB p.liveShared_of_new_mixed,?_⟩
  intro hCard hPath
  obtain ⟨u,hu,hU⟩ := p.reachable_liveShared hPath
  exact hU.trans (p.reachable_right_of_split p.new hS (fun h ↦ p.new_partition h) hR hB
    p.liveShared_of_new_mixed p.newSurvives_map_le
    ⟨S.right,rfl,p.right_incident_or_liveShared hIncident⟩ hCard hu)

end LovaszTheta.Independent.Identification
