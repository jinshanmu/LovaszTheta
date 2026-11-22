module

public import LovaszTheta.ProperLastCancellation

/-!
# Exact last-block cancellation

Canceling exactly the last block leaves the prefix graph. The
only shared vertices that can remain are the junction with that
prefix and the new right boundary.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

lemma reachable_map_lift {F V : Type*} (e : F ↪ V) {G : SimpleGraph F} {a : F} {w : V}
    (h : (G.map e).Reachable (e a) w) : ∃ b, e b = w ∧ G.Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨a,rfl,Reachable.refl _⟩
  | @tail u v _ he ih =>
    obtain ⟨b,hb,hReach⟩ := ih
    obtain ⟨c,d,hEdge,hC,hD⟩ := (SimpleGraph.map_adj e G _ _).mp he
    have hEq := e.injective (hC.trans hb.symm)
    exact ⟨d,hD,hReach.trans (hEq ▸ hEdge).reachable⟩

namespace ChainTerm

lemma right_reachable_of_single (P : ChainTerm) (h : P.leftChain = none) :
    P.graph.Reachable P.toShape.left P.toShape.right :=
  P.reachable_rightBoundary (by rw [(P.offset_eq_zero_iff).mpr h]; exact Nat.zero_le _)

lemma right_incident_of_ne_empty (P : ChainTerm) (h : P.rightChain ≠ []) :
    Incident P.toShape.graph P.toShape.right := by
  let L := Chain.span P.rightChain
  have hL : 0 < L := Nat.pos_of_ne_zero (fun he ↦ h ((Chain.span_eq_zero_iff _).mp he))
  have hSub : L-1+1 = L := by omega
  let a : Fin P.toShape.vertexCount := ⟨P.offset+(L-1),by change P.offset+(L-1) < L+P.offset+1; omega⟩
  refine ⟨a,Or.inr ⟨L,L-1,Nat.add_comm _ _,rfl,?_⟩⟩
  apply adjAt_symm
  have he := Chain.adjAt_succ P.rightChain (show L-1+1 ≤ L by omega)
  simpa only [hSub] using he

variable (P : ChainTerm) (T S : BasicShape)
variable (p : Identification (P.append T).toShape S.toShape)

/-- The left endpoint of the canceled block, in the quotient. -/
def junction : p.Vertex := P.lastInQuotient T S p 0

lemma prefix_right_eq_junction :
    P.prefixInQuotient T S p P.toShape.right = P.junction T S p := by
  apply congrArg p.old
  apply Fin.ext
  change 0+P.span = P.span+0
  simp

lemma prefix_left_eq_output :
    P.prefixInQuotient T S p P.toShape.left = p.outputLeft := by
  apply congrArg p.old
  exact Fin.ext rfl

lemma eq_junction_of_prefix_of_last {u : p.Vertex}
    (hP : u ∈ Set.range (P.prefixInQuotient T S p))
    (hT : u ∈ Set.range (P.lastInQuotient T S p)) : u = P.junction T S p := by
  obtain ⟨a,rfl⟩ := hP
  obtain ⟨b,hb⟩ := hT
  have he : P.tailEmb T b = P.prefixEmb T a := p.old.injective hb
  have hV := congrArg Fin.val he
  change P.span + b.val = 0+a.val at hV
  have ha := a.isLt
  have hEq : b = 0 := Fin.ext (by change b.val = 0; omega)
  subst b
  exact hb.symm

lemma prefixGraph_disjoint_lastGraph {u v : p.Vertex}
    (hP : (P.graph.map (P.prefixInQuotient T S p)).Adj u v) : ¬(P.lastGraph T S p).Adj u v := by
  intro hT
  obtain ⟨a,b,_,ha,hb⟩ := (SimpleGraph.map_adj (P.prefixInQuotient T S p) _ _ _).mp hP
  obtain ⟨c,d,_,hc,hd⟩ := (SimpleGraph.map_adj (P.lastInQuotient T S p) _ _ _).mp hT
  exact hP.ne ((P.eq_junction_of_prefix_of_last T S p ⟨a,ha⟩ ⟨c,hc⟩).trans
    (P.eq_junction_of_prefix_of_last T S p ⟨b,hb⟩ ⟨d,hd⟩).symm)

lemma remaining_eq_prefix_of_exact (h : p.newGraph = P.lastGraph T S p) :
    p.remaining = P.graph.map (P.prefixInQuotient T S p) := by
  unfold Identification.remaining
  rw [P.oldGraph_eq_prefix_sup_last T S p,h]
  ext u v
  constructor
  · rintro (⟨hP | hT,hn⟩ | ⟨hT,hn⟩)
    · exact hP
    · exact (hn hT).elim
    · exact (hn (Or.inr hT)).elim
  · exact fun hP ↦ Or.inl ⟨Or.inl hP,P.prefixGraph_disjoint_lastGraph T S p hP⟩

lemma range_new_eq_range_last (h : p.newGraph = P.lastGraph T S p) :
    Set.range p.new = Set.range (P.lastInQuotient T S p) := by
  apply Set.Subset.antisymm (P.new_range_subset_last_range T S p h.le)
  rintro _ ⟨a,rfl⟩
  obtain ⟨b,hb⟩ := T.incident_pathGraph a
  have he : p.newGraph.Adj (P.lastInQuotient T S p a) (P.lastInQuotient T S p b) :=
    h.symm ▸ SimpleGraph.map_adj_apply.mpr hb
  exact p.mem_new_of_newAdj he

lemma shared_iff_range_last (h : p.newGraph = P.lastGraph T S p) {u : p.Vertex} :
    u ∈ p.shared ↔ u ∈ Set.range (P.lastInQuotient T S p) := by
  rw [p.mem_shared,P.range_new_eq_range_last T S p h]
  exact and_iff_right_of_imp (fun ⟨a,ha⟩ ↦ ⟨P.tailEmb T a,ha⟩)

lemma outputRight_mem_range_last (h : p.newGraph = P.lastGraph T S p) :
    p.outputRight ∈ Set.range (P.lastInQuotient T S p) :=
  (P.range_new_eq_range_last T S p h) ▸ Set.mem_range_self S.toShape.right

lemma size_eq_of_exact (h : p.newGraph = P.lastGraph T S p) : S.span = T.span := by
  have he := Fintype.card_congr (Set.equivOfEq (P.range_new_eq_range_last T S p h))
  rw [Fintype.card_range,Fintype.card_range,Fintype.card_fin,Fintype.card_fin] at he
  change S.span+1 = T.span+1 at he
  omega

lemma quotient_size_of_exact (h : p.newGraph = P.lastGraph T S p) :
    p.shape.vertexCount = (P.append T).toShape.vertexCount := by
  have hs : Function.Surjective p.old := by
    intro u
    rcases p.vertex_in_factors u with hP | hS
    · exact hP
    · rw [P.range_new_eq_range_last T S p h] at hS
      obtain ⟨a,ha⟩ := hS
      exact ⟨P.tailEmb T a,ha⟩
  exact (Fintype.card_congr (Equiv.ofBijective p.old ⟨p.old.injective,hs⟩)).symm.trans (Fintype.card_fin _)

/-- Whether the junction would remain if the new right boundary is elsewhere. -/
def keepsJunction (P : ChainTerm) : Prop := P.leftChain = none ∨ P.rightChain ≠ []

lemma junction_eq_left_iff :
    P.junction T S p = p.outputLeft ↔ P.span = 0 := by
  rw [← P.prefix_right_eq_junction T S p,← P.prefix_left_eq_output T S p]
  constructor
  · intro h
    exact congrArg Fin.val ((P.prefixInQuotient T S p).injective h)
  · intro h
    exact congrArg (P.prefixInQuotient T S p) (Fin.ext h)

lemma junction_incident_or_left :
    Incident (P.graph.map (P.prefixInQuotient T S p)) (P.junction T S p) ∨
      P.junction T S p = p.outputLeft ↔ P.keepsJunction := by
  rw [P.junction_eq_left_iff T S p]
  constructor
  · rintro (⟨v,h⟩ | h)
    · obtain ⟨a,b,he,ha,hb⟩ := (SimpleGraph.map_adj (P.prefixInQuotient T S p) _ _ _).mp h
      rw [← P.prefix_right_eq_junction T S p] at ha
      have he' := (P.prefixInQuotient T S p).injective ha
      exact Or.inr (fun hP ↦ P.not_incident_right_of_empty hP ⟨b,he' ▸ he⟩)
    · exact Or.inl ((P.offset_eq_zero_iff).mp (by change Chain.span P.rightChain+P.offset = 0 at h; omega))
  · rintro (h | h)
    · by_cases hR : P.rightChain = []
      · exact Or.inr (by simp [hR,h,offset])
      · obtain ⟨b,hb⟩ := P.right_incident_of_ne_empty hR
        rw [← P.prefix_right_eq_junction T S p]
        exact Or.inl ⟨_,SimpleGraph.map_adj_apply.mpr hb⟩
    · obtain ⟨b,hb⟩ := P.right_incident_of_ne_empty h
      rw [← P.prefix_right_eq_junction T S p]
      exact Or.inl ⟨_,SimpleGraph.map_adj_apply.mpr hb⟩

lemma liveShared_iff_of_exact (h : p.newGraph = P.lastGraph T S p) {u : p.Vertex} :
    u ∈ p.liveShared ↔ u = p.outputRight ∨ (u = P.junction T S p ∧ P.keepsJunction) := by
  rw [p.mem_liveShared,P.shared_iff_range_last T S p h,P.remaining_eq_prefix_of_exact T S p h]
  let e := P.prefixInQuotient T S p
  constructor
  · rintro ⟨hT,hP | hL | hR⟩
    · obtain ⟨w,hw⟩ := hP
      obtain ⟨a,b,he,ha,hb⟩ := (SimpleGraph.map_adj e _ _ _).mp hw
      have hEq : u = P.junction T S p := P.eq_junction_of_prefix_of_last T S p ⟨a,ha⟩ hT
      exact Or.inr ⟨hEq,(P.junction_incident_or_left T S p).mp (Or.inl ⟨w,hEq ▸ hw⟩)⟩
    · have hEq : u = P.junction T S p := P.eq_junction_of_prefix_of_last T S p
        ⟨P.toShape.left,(P.prefix_left_eq_output T S p).trans hL.symm⟩ hT
      exact Or.inr ⟨hEq,(P.junction_incident_or_left T S p).mp (Or.inr (hEq.symm.trans hL))⟩
    · exact Or.inl hR
  · rintro (rfl | ⟨rfl,hKeep⟩)
    · exact ⟨P.outputRight_mem_range_last T S p h,Or.inr (Or.inr rfl)⟩
    · exact ⟨⟨0,rfl⟩,((P.junction_incident_or_left T S p).mpr hKeep).elim Or.inl
        (fun he ↦ Or.inr (Or.inl he))⟩

lemma outputRight_not_in_prefix (h : p.newGraph = P.lastGraph T S p)
    (hW : p.outputRight ≠ P.junction T S p) :
    p.outputRight ∉ Set.range (P.prefixInQuotient T S p) :=
  fun hP ↦ hW (P.eq_junction_of_prefix_of_last T S p hP (P.outputRight_mem_range_last T S p h))

lemma reachable_iff_of_exact (h : p.newGraph = P.lastGraph T S p) :
    p.remaining.Reachable p.outputLeft p.outputRight ↔
      p.outputRight = P.junction T S p ∧ P.graph.Reachable P.toShape.left P.toShape.right := by
  rw [P.remaining_eq_prefix_of_exact T S p h,← P.prefix_left_eq_output T S p]
  let e := P.prefixInQuotient T S p
  constructor
  · intro hR
    obtain ⟨u,hu,hR'⟩ := reachable_map_lift e hR
    have hW := P.eq_junction_of_prefix_of_last T S p ⟨u,hu⟩ (P.outputRight_mem_range_last T S p h)
    have hEq : u = P.toShape.right := e.injective ((hu.trans hW).trans (P.prefix_right_eq_junction T S p).symm)
    exact ⟨hW,hEq ▸ hR'⟩
  · rintro ⟨hW,hR⟩
    rw [hW,← P.prefix_right_eq_junction T S p]
    exact hR.map (SimpleGraph.Embedding.map e P.graph).toHom

end ChainTerm

end LovaszTheta.Independent
