module

public import LovaszTheta.TraceBlockTypes

/-!
# Pairing blocks in the trace

A first later edge overlap with a return block must contain all
edges of the forward block unless it has two middle labels.
If the inclusion is strict, the last earlier overlap of the return
block has two middle labels.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {I V : Type*} [Fintype I] [LinearOrder I]

/-- Two blocks share a labeled edge. -/
def ShareEdge (b : I → LabeledBlock V) (i j : I) : Prop :=
  ∃ u v, (b i).graph.Adj u v ∧ (b j).graph.Adj u v

omit [Fintype I] [LinearOrder I] in
lemma ShareEdge.symm {b : I → LabeledBlock V} {i j : I} (h : ShareEdge b i j) : ShareEdge b j i := by
  obtain ⟨u,v,h₁,h₂⟩ := h
  exact ⟨u,v,h₂,h₁⟩

/-- None of this block's edges have occurred earlier. -/
def firstEdges (b : I → LabeledBlock V) (i : I) : Prop := ∀ j < i, ¬ShareEdge b i j

/-- None of this block's edges occur later. -/
def lastEdges (b : I → LabeledBlock V) (i : I) : Prop := ∀ j, i < j → ¬ShareEdge b i j

/-- The positions where the middle-label count is at most one. -/
def simplePosition (b : I → LabeledBlock V) (i : I) : Prop :=
  (middleLabels (fun j ↦ (b j).vertices) i).card ≤ 1

/-- An overlap with no earlier overlap after the starting block. -/
def firstLaterOverlap (b : I → LabeledBlock V) (i j : I) : Prop :=
  i < j ∧ ShareEdge b i j ∧ ∀ k, i < k → k < j → ¬ShareEdge b i k

/-- An overlap with no later overlap before the ending block. -/
def lastEarlierOverlap (b : I → LabeledBlock V) (i j : I) : Prop :=
  i < j ∧ ShareEdge b i j ∧ ∀ k, i < k → k < j → ¬ShareEdge b j k

/-- The two simple positions of one edge-for-edge pair. -/
def exactPair (b : I → LabeledBlock V) (i j : I) : Prop :=
  i < j ∧ simplePosition b i ∧ simplePosition b j ∧ (b i).graph = (b j).graph ∧
    ∀ k, k ≠ i → k ≠ j → ¬ShareEdge b i k

/-- The position is adjacent to an exceptional position by at most
two shared edges, with a simple intermediate position. -/
def nearExceptional (b : I → LabeledBlock V) (i : I) : Prop :=
  (∃ j, ShareEdge b i j ∧ ¬simplePosition b j) ∨
    ∃ j k, ShareEdge b i j ∧ simplePosition b j ∧ ShareEdge b j k ∧ ¬simplePosition b k

private lemma mem_middleLabels_iff_occurs (b : I → LabeledBlock V) (i : I) (u : V) :
    u ∈ middleLabels (fun j ↦ (b j).vertices) i ↔
      u ∈ (b i).vertices ∧ (∃ j, j < i ∧ u ∈ (b j).vertices) ∧ (∃ j, i < j ∧ u ∈ (b j).vertices) := by
  simp only [middleLabels,middle,occurrences,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨hi,⟨_,⟨j,hj,hji⟩,k,hk,hik⟩⟩
    exact ⟨hi,⟨j,hji,hj⟩,k,hik,hk⟩
  · rintro ⟨hi,⟨j,hji,hj⟩,k,hik,hk⟩
    exact ⟨hi,hi,⟨j,hj,hji⟩,k,hk,hik⟩

private lemma not_simplePosition_of_two_middle {b : I → LabeledBlock V} {j : I} {u v : V}
    (huv : u ≠ v) (hu : u ∈ middleLabels (fun j ↦ (b j).vertices) j)
    (hv : v ∈ middleLabels (fun j ↦ (b j).vertices) j) : ¬simplePosition b j := by
  intro hj
  have h : ({u,v} : Finset V) ⊆ middleLabels (fun j ↦ (b j).vertices) j := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hu
    · rw [mem_singleton.mp hw]
      exact hv
  have hc := card_le_card h
  rw [card_pair huv] at hc
  unfold simplePosition at hj
  omega

/-- The earliest of the later edge overlaps. -/
lemma exists_firstLaterOverlap {b : I → LabeledBlock V} {i : I}
    (h : ∃ j, i < j ∧ ShareEdge b i j) : ∃ j, firstLaterOverlap b i j := by
  let S := univ.filter fun j ↦ i < j ∧ ShareEdge b i j
  have hS : S.Nonempty := by
    obtain ⟨j,hj,hShare⟩ := h
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,hj,hShare⟩⟩
  let j := S.min' hS
  have hj := (mem_filter.mp (min'_mem S hS)).2
  refine ⟨j,hj.1,hj.2,fun k hk hkj hShare ↦ ?_⟩
  exact (not_lt_of_ge (min'_le S k (mem_filter.mpr ⟨mem_univ _,hk,hShare⟩))) hkj

/-- The latest of the earlier edge overlaps. -/
lemma exists_lastEarlierOverlap {b : I → LabeledBlock V} {j : I}
    (h : ∃ i, i < j ∧ ShareEdge b i j) : ∃ i, lastEarlierOverlap b i j := by
  let S := univ.filter fun i ↦ i < j ∧ ShareEdge b i j
  have hS : S.Nonempty := by
    obtain ⟨i,hi,hShare⟩ := h
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi,hShare⟩⟩
  let i := S.max' hS
  have hi := (mem_filter.mp (max'_mem S hS)).2
  refine ⟨i,hi.1,hi.2,fun k hik hkj hShare ↦ ?_⟩
  exact (not_lt_of_ge (le_max' S k (mem_filter.mpr ⟨mem_univ _,hkj,hShare.symm⟩))) hik

variable (b : I → LabeledBlock V)

private lemma subset_of_simple_firstLaterOverlap
    (repeatEdges : ∀ i u v, (b i).graph.Adj u v → ∃ j, j ≠ i ∧ (b j).graph.Adj u v)
    {i j : I} (hi : firstEdges b i) (hij : firstLaterOverlap b i j) (hj : simplePosition b j) :
    (b i).graph ≤ (b j).graph := by
  intro u v e
  by_contra hn
  obtain ⟨a,c,hac,ha,hc⟩ := (b i).exists_two_mixed_of_partial_overlap (b j).graph hij.2.1 ⟨u,v,e,hn⟩
  have hMiddle (w : V) (hw : Mixed ((b i).graph ⊓ (b j).graph) ((b i).graph \ (b j).graph) w) :
      w ∈ middleLabels (fun k ↦ (b k).vertices) j := by
    obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := hw
    obtain ⟨k,hki,hk⟩ := repeatEdges i w q hq.1
    have hIK : i < k := by
      rcases lt_or_gt_of_ne hki with hk' | hk'
      · exact (hi k hk' ⟨w,q,hq.1,hk⟩).elim
      · exact hk'
    have hJK : j < k := by
      rcases lt_trichotomy k j with hlt | rfl | hgt
      · exact (hij.2.2 k hIK hlt ⟨w,q,hq.1,hk⟩).elim
      · exact (hq.2 hk).elim
      · exact hgt
    exact (mem_middleLabels_iff_occurs b j w).mpr ⟨LabeledBlock.mem_vertices_of_adj hp.2,
      ⟨i,hij.1,LabeledBlock.mem_vertices_of_adj hp.1⟩,k,hJK,LabeledBlock.mem_vertices_of_adj hk⟩
  exact not_simplePosition_of_two_middle hac (hMiddle a ha) (hMiddle c hc) hj

private lemma not_simple_of_partial_lastEarlierOverlap
    (repeatEdges : ∀ i u v, (b i).graph.Adj u v → ∃ j, j ≠ i ∧ (b j).graph.Adj u v)
    {j k : I} (hj : lastEdges b j) (hkj : lastEarlierOverlap b k j)
    (hMiss : ∃ u v, (b j).graph.Adj u v ∧ ¬(b k).graph.Adj u v) : ¬simplePosition b k := by
  obtain ⟨a,c,hac,ha,hc⟩ := (b j).exists_two_mixed_of_partial_overlap (b k).graph hkj.2.1.symm hMiss
  have hMiddle (w : V) (hw : Mixed ((b j).graph ⊓ (b k).graph) ((b j).graph \ (b k).graph) w) :
      w ∈ middleLabels (fun r ↦ (b r).vertices) k := by
    obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := hw
    obtain ⟨r,hrj,hr⟩ := repeatEdges j w q hq.1
    have hRJ : r < j := by
      rcases lt_or_gt_of_ne hrj with hr' | hr'
      · exact hr'
      · exact (hj r hr' ⟨w,q,hq.1,hr⟩).elim
    have hRK : r < k := by
      rcases lt_trichotomy k r with hlt | rfl | hgt
      · exact (hkj.2.2 r hlt hRJ ⟨w,q,hq.1,hr⟩).elim
      · exact (hq.2 hr).elim
      · exact hgt
    exact (mem_middleLabels_iff_occurs b k w).mpr ⟨LabeledBlock.mem_vertices_of_adj hp.2,
      ⟨r,hRK,LabeledBlock.mem_vertices_of_adj hr⟩,j,hkj.1,LabeledBlock.mem_vertices_of_adj hp.1⟩
  exact not_simplePosition_of_two_middle hac (hMiddle a ha) (hMiddle c hc)

/-- A simple block whose edges are all new either has an exact
partner or is within two edge overlaps of an exceptional block. -/
theorem exactPair_or_nearExceptional_of_first
    (repeatEdges : ∀ i u v, (b i).graph.Adj u v → ∃ j, j ≠ i ∧ (b j).graph.Adj u v)
    (hClass : ∀ i, simplePosition b i → firstEdges b i ∨ lastEdges b i)
    {i : I} (hi : simplePosition b i) (hFirst : firstEdges b i) :
    (∃ j, exactPair b i j) ∨ nearExceptional b i := by
  obtain ⟨j,hij⟩ : ∃ j, firstLaterOverlap b i j := by
    obtain ⟨j,hj,h⟩ := repeatEdges i _ _ (b i).graph_adj_left_right
    have hS : ShareEdge b i j := ⟨_,_,(b i).graph_adj_left_right,h⟩
    have hj' : i < j := lt_of_le_of_ne (le_of_not_gt (fun hlt ↦ hFirst j hlt hS)) hj.symm
    exact exists_firstLaterOverlap ⟨j,hj',hS⟩
  by_cases hj : simplePosition b j
  · have hLast : lastEdges b j := (hClass j hj).resolve_left (fun he ↦ he i hij.1 hij.2.1.symm)
    have hSub := subset_of_simple_firstLaterOverlap b repeatEdges hFirst hij hj
    by_cases hEq : (b i).graph = (b j).graph
    · refine Or.inl ⟨j,hij.1,hi,hj,hEq,?_⟩
      intro k hki hkj
      rcases lt_or_gt_of_ne hki with hk | hk
      · exact hFirst k hk
      rcases lt_or_gt_of_ne hkj with hlt | hlt
      · exact hij.2.2 k hk hlt
      · simpa only [ShareEdge,hEq] using hLast k hlt
    · obtain ⟨k,hkj⟩ := exists_lastEarlierOverlap (b := b) (j := j) ⟨i,hij.1,hij.2.1⟩
      have hik : i ≤ k := le_of_not_gt (fun h ↦ hkj.2.2 i h hij.1 hij.2.1.symm)
      have hMiss : ∃ u v, (b j).graph.Adj u v ∧ ¬(b k).graph.Adj u v := by
        by_cases hki : k = i
        · subst k
          by_contra! hAll
          exact hEq (le_antisymm hSub hAll)
        · obtain ⟨u,v,he,he'⟩ := hij.2.1
          exact ⟨u,v,he',fun hk ↦ hij.2.2 k (lt_of_le_of_ne hik (Ne.symm hki)) hkj.1 ⟨u,v,he,hk⟩⟩
      exact Or.inr (Or.inr ⟨j,k,hij.2.1,hj,hkj.2.1.symm,
        not_simple_of_partial_lastEarlierOverlap b repeatEdges hLast hkj hMiss⟩)
  · exact Or.inr (Or.inl ⟨j,hij.2.1,hj⟩)

/-- Reversing time gives the same alternative for the last block of a repeated edge. -/
theorem exactPair_or_nearExceptional_of_last
    (repeatEdges : ∀ i u v, (b i).graph.Adj u v → ∃ j, j ≠ i ∧ (b j).graph.Adj u v)
    (hClass : ∀ i, simplePosition b i → firstEdges b i ∨ lastEdges b i)
    {i : I} (hi : simplePosition b i) (hLast : lastEdges b i) :
    (∃ j, exactPair b j i) ∨ nearExceptional b i := by
  let d : Iᵒᵈ → LabeledBlock V := fun j ↦ b (OrderDual.ofDual j)
  have hSimple (j : Iᵒᵈ) : simplePosition d j ↔ simplePosition b (OrderDual.ofDual j) := by
    unfold simplePosition
    have he : middleLabels (fun k ↦ (d k).vertices) j =
        middleLabels (fun k ↦ (b k).vertices) (OrderDual.ofDual j) := by
      ext u
      rw [mem_middleLabels_iff_occurs,mem_middleLabels_iff_occurs]
      change u ∈ (b (OrderDual.ofDual j)).vertices ∧
        (∃ k : I, OrderDual.ofDual j < k ∧ u ∈ (b k).vertices) ∧
        (∃ k : I, k < OrderDual.ofDual j ∧ u ∈ (b k).vertices) ↔ _
      exact and_congr_right fun _ ↦ and_comm
    rw [he]
  have hDual : ∀ j, simplePosition d j → firstEdges d j ∨ lastEdges d j := by
    intro j hj
    exact (hClass (OrderDual.ofDual j) ((hSimple j).mp hj)).symm
  have h := exactPair_or_nearExceptional_of_first d repeatEdges hDual
    ((hSimple (OrderDual.toDual i)).mpr hi) (show firstEdges d (OrderDual.toDual i) from hLast)
  rcases h with ⟨j,h⟩ | h
  · obtain ⟨hj,_,hSimpleJ,hEq,hOne⟩ := h
    refine Or.inl ⟨OrderDual.ofDual j,hj,(hSimple j).mp hSimpleJ,hi,hEq.symm,?_⟩
    intro k hkj hki hShare
    have he : ShareEdge d (OrderDual.toDual i) (OrderDual.toDual k) := by
      have hE : (b i).graph = (b (OrderDual.ofDual j)).graph := hEq
      change ShareEdge b i k
      unfold ShareEdge
      rw [hE]
      exact hShare
    exact hOne (OrderDual.toDual k) hki hkj he
  · rcases h with ⟨j,he,hj⟩ | ⟨j,k,he,hj,hf,hk⟩
    · exact Or.inr (Or.inl ⟨OrderDual.ofDual j,he,fun h ↦ hj ((hSimple j).mpr h)⟩)
    · exact Or.inr (Or.inr ⟨OrderDual.ofDual j,OrderDual.ofDual k,he,(hSimple j).mp hj,hf,
        fun h ↦ hk ((hSimple k).mpr h)⟩)

namespace TraceBlocks

variable {l : ℕ} {c : TraceBlocks V (l+2)}

/-- Forward and return positions have, respectively, only first and only last edges. -/
lemma firstEdges_or_lastEdges (h : c.RepeatedEdges) (i : Fin (l+2))
    (hi : simplePosition c.block i) : firstEdges c.block i ∨ lastEdges c.block i := by
  rcases forward_or_return h hi with hF | hR
  · refine Or.inl (fun j hj ↦ ?_)
    rintro ⟨u,v,he,hj'⟩
    exact edge_of_forward_not_earlier hF hj he hj'
  · refine Or.inr (fun j hj ↦ ?_)
    rintro ⟨u,v,he,hj'⟩
    exact edge_of_return_not_later hR hj he hj'

/-- An unpaired position with at most one middle label has a nearby exceptional block. -/
theorem nearExceptional_of_unpaired (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hi : simplePosition c.block i)
    (hNone : ¬∃ j, exactPair c.block i j ∨ exactPair c.block j i) :
    nearExceptional c.block i := by
  have hClass := firstEdges_or_lastEdges h
  rcases hClass i hi with hf | hr
  · exact (exactPair_or_nearExceptional_of_first c.block h hClass hi hf).resolve_left
      (fun ⟨j,hj⟩ ↦ hNone ⟨j,Or.inl hj⟩)
  · exact (exactPair_or_nearExceptional_of_last c.block h hClass hi hr).resolve_left
      (fun ⟨j,hj⟩ ↦ hNone ⟨j,Or.inr hj⟩)

/-- Exact pairs have a forward first member and a return second member. -/
theorem forward_return_of_exactPair (h : c.RepeatedEdges) {i j : Fin (l+2)}
    (he : exactPair c.block i j) : c.Forward i ∧ c.Return j := by
  have hEdge : (c.block j).graph.Adj (c.block i).left (c.block i).right :=
    he.2.2.2.1 ▸ (c.block i).graph_adj_left_right
  exact ⟨(forward_or_return h he.2.1).resolve_right (fun hr ↦
    edge_of_return_not_later hr he.1 (c.block i).graph_adj_left_right hEdge),
    (forward_or_return h he.2.2.1).resolve_left (fun hf ↦
      edge_of_forward_not_earlier hf he.1 hEdge (c.block i).graph_adj_left_right)⟩

end TraceBlocks

end LovaszTheta.Independent
