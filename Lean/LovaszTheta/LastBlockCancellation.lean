module

public import LovaszTheta.ChainTerms
public import LovaszTheta.PartialCancellation

/-!
# Cancellation inside the last block

If all edges of the multiplying block cancel, its vertex-deleted
connectivity keeps it on one side of each articulation. Because it
contains the old right boundary, it lies wholly in the last block.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

namespace BasicShape

lemma incident (T : BasicShape) (u : Fin T.toShape.vertexCount) : Incident T.graph u := by
  change Fin (T.additionalVertices+2) at u
  exact ⟨u+1,T.cycle_le (cycleGraph_adj.mpr (Or.inr (by abel)))⟩

lemma preconnected (T : BasicShape) : T.graph.Preconnected :=
  preconnected_cycleGraph.mono T.cycle_le

end BasicShape

private lemma stays_below {F : Type*} {r : F → F → Prop} (pos : F → ℕ) (c : ℕ)
    (hAvoid : ∀ u, pos u ≠ c) (hStep : ∀ {u v}, r u v → pos u < c → ¬c < pos v)
    {a b : F} (h : Relation.ReflTransGen r a b) (ha : pos a < c) : pos b < c := by
  induction h with
  | refl => exact ha
  | @tail u v _ he ih =>
    have h₁ := hStep he ih
    have h₂ := hAvoid v
    omega

private lemma le_positions_of_vertexDeletionConnected {F : Type*}
    {G : SimpleGraph F} (hPre : G.Preconnected) (hDel : VertexDeletionConnected G)
    (pos : F → ℕ) (hInj : Function.Injective pos) (c : ℕ)
    (hStep : ∀ {u v}, G.Adj u v → pos u < c → ¬c < pos v) {b : F} (hb : c < pos b)
    (a : F) : c ≤ pos a := by
  by_contra! ha
  by_cases h : ∃ d, pos d = c
  · obtain ⟨d,hd⟩ := h
    let a' : {u : F // u ≠ d} := ⟨a,fun he ↦ by subst a; omega⟩
    let b' : {u : F // u ≠ d} := ⟨b,fun he ↦ by subst b; omega⟩
    have hReach := hDel d a' b'
    rw [SimpleGraph.reachable_iff_reflTransGen] at hReach
    have hAvoid (u : {x : F // x ≠ d}) : pos u.val ≠ c :=
      fun he ↦ u.property (hInj (he.trans hd.symm))
    have hBelow : pos b < c := stays_below (pos ∘ Subtype.val) c hAvoid
      (fun he hLt ↦ hStep he hLt) hReach ha
    omega
  · have hReach := hPre a b
    rw [SimpleGraph.reachable_iff_reflTransGen] at hReach
    have hBelow := stays_below pos c (fun u he ↦ h ⟨u,he⟩) hStep hReach ha
    omega

lemma ChainTerm.no_cross_last_cut (P : ChainTerm) (T : BasicShape)
    {a b : Fin ((P.append T).span+1)} (ha : a.val < P.span) (hb : P.span < b.val) :
    ¬(P.append T).graph.Adj a b := by
  intro h
  have h' := (P.adjAt_append T _ _).mp ((adjAt_iff_adj _ _ _).mpr h)
  rcases h' with ⟨_,hB,_⟩ | ⟨_,_,hA,_,_⟩
  · omega
  · omega

lemma ChainTerm.not_incident_right_of_empty (P : ChainTerm) (hP : P.rightChain = []) :
    ¬Incident P.toShape.graph P.toShape.right := by
  rintro ⟨w,h⟩
  have he := (P.adjAt_iff _ _).mp ((adjAt_iff_adj P.graph _ _).mpr h)
  rcases he with ⟨L,hL,he⟩ | ⟨u,v,_,_,he⟩
  · have hBound : P.span = Chain.span L+1 := by simp [span,offset,hL,hP]
    have hlt := he.choose
    change P.span < Chain.span L+1 at hlt
    omega
  · rw [hP] at he
    obtain ⟨_,_,he⟩ := he
    exact he

namespace Identification

variable {P S : Shape} (p : Identification P S)

lemma newGraph_le_oldGraph_of_no_survivors (h : ¬∃ a, Incident p.newSurvives a) :
    p.newGraph ≤ p.oldGraph := by
  intro u v hu
  obtain ⟨a,b,he,rfl,rfl⟩ := (SimpleGraph.map_adj p.new S.graph _ _).mp hu
  rcases p.new_partition he with hR | hB
  · exact (h ⟨a,b,hR⟩).elim
  · exact hB.2

/-- Locate each vertex of the multiplying block in the old factor when all its edges cancel. -/
noncomputable def containedEmbedding (h : p.newGraph ≤ p.oldGraph) (hS : ∀ a, Incident S.graph a) :
    Fin S.vertexCount ↪ Fin P.vertexCount := by
  have hMem (a : Fin S.vertexCount) : ∃ i, p.old i = p.new a := by
    obtain ⟨b,hb⟩ := hS a
    exact p.mem_old_of_oldAdj (h (SimpleGraph.map_adj_apply.mpr hb))
  exact ⟨fun a ↦ (hMem a).choose,fun a b he ↦ p.new.injective
    (((hMem a).choose_spec.symm.trans (congrArg p.old he)).trans (hMem b).choose_spec)⟩

lemma old_containedEmbedding (h : p.newGraph ≤ p.oldGraph) (hS : ∀ a, Incident S.graph a)
    (a : Fin S.vertexCount) : p.old (p.containedEmbedding h hS a) = p.new a := by
  have hMem : ∃ i, p.old i = p.new a := by
    obtain ⟨b,hb⟩ := hS a
    exact p.mem_old_of_oldAdj (h (SimpleGraph.map_adj_apply.mpr hb))
  change p.old hMem.choose = p.new a
  exact hMem.choose_spec

lemma containedEmbedding_left (h : p.newGraph ≤ p.oldGraph) (hS : ∀ a, Incident S.graph a) :
    p.containedEmbedding h hS S.left = P.right :=
  p.old.injective ((p.old_containedEmbedding h hS _).trans p.join)

lemma containedEmbedding_adj (h : p.newGraph ≤ p.oldGraph) (hS : ∀ a, Incident S.graph a)
    {a b : Fin S.vertexCount} (he : S.graph.Adj a b) :
    P.graph.Adj (p.containedEmbedding h hS a) (p.containedEmbedding h hS b) :=
  SimpleGraph.map_adj_apply.mp
    (by rw [p.old_containedEmbedding h hS,p.old_containedEmbedding h hS]
        exact h (SimpleGraph.map_adj_apply.mpr he))

end Identification

namespace ChainTerm

variable (P : ChainTerm) (T S : BasicShape)
variable (p : Identification (P.append T).toShape S.toShape)

/-- The remaining prefix, embedded in the quotient of the product. -/
def prefixInQuotient : Fin (P.span+1) ↪ p.Vertex := (P.prefixEmb T).trans p.old

/-- The last block of the old chain, embedded in the quotient of the product. -/
def lastInQuotient : Fin (T.span+1) ↪ p.Vertex := (P.tailEmb T).trans p.old

lemma oldGraph_eq_prefix_sup_last :
    p.oldGraph = (P.graph.map (P.prefixInQuotient T S p)) ⊔
      (T.pathGraph.map (P.lastInQuotient T S p)) := by
  unfold Identification.oldGraph
  change ((P.append T).graph.map p.old) = _
  rw [P.graph_append T]
  ext a b
  simp only [sup_adj]
  rw [SimpleGraph.map_adj p.old]
  simp only [sup_adj]
  unfold prefixInQuotient lastInQuotient
  rw [show (P.graph.map ((P.prefixEmb T).trans p.old)) =
      (P.graph.map (P.prefixEmb T)).map p.old by rw [SimpleGraph.map_map]; rfl]
  rw [show (T.pathGraph.map ((P.tailEmb T).trans p.old)) =
      (T.pathGraph.map (P.tailEmb T)).map p.old by rw [SimpleGraph.map_map]; rfl]
  simp only [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u,v,h | h,hu,hv⟩
    · exact Or.inl ⟨u,v,h,hu,hv⟩
    · exact Or.inr ⟨u,v,h,hu,hv⟩
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · exact ⟨u,v,Or.inl h,hu,hv⟩
    · exact ⟨u,v,Or.inr h,hu,hv⟩

/-- Complete cancellation in a product can only use edges of the last block. -/
theorem newGraph_le_last_of_le_old (h : p.newGraph ≤ p.oldGraph) :
    p.newGraph ≤ T.pathGraph.map (P.lastInQuotient T S p) := by
  let e := p.containedEmbedding h S.incident
  have hLeft : (e S.toShape.left).val = (P.append T).span :=
    congrArg Fin.val (p.containedEmbedding_left h S.incident)
  have hGt : P.span < (e S.toShape.left).val := by
    have hPos := T.span_pos
    rw [hLeft,P.span_append]
    omega
  have hInj : Function.Injective (fun a ↦ (e a).val) := Fin.val_injective.comp e.injective
  have hCut {a b : Fin S.toShape.vertexCount} (he : S.graph.Adj a b) (ha : (e a).val < P.span) :
      ¬P.span < (e b).val :=
    fun hb ↦ P.no_cross_last_cut T ha hb (p.containedEmbedding_adj h S.incident he)
  have hAll : ∀ a, P.span ≤ (e a).val := le_positions_of_vertexDeletionConnected S.preconnected
    S.vertexDeletionConnected _ hInj _ hCut hGt
  intro u v he
  obtain ⟨a,b,hS,rfl,rfl⟩ := (SimpleGraph.map_adj p.new S.graph _ _).mp he
  have hOld := h (SimpleGraph.map_adj_apply.mpr hS : p.newGraph.Adj (p.new a) (p.new b))
  rw [P.oldGraph_eq_prefix_sup_last T S p] at hOld
  rcases hOld with hp | ht
  · obtain ⟨x,y,hxy,hX,hY⟩ := (SimpleGraph.map_adj (P.prefixInQuotient T S p) P.graph _ _).mp hp
    have he₁ : P.prefixEmb T x = e a := p.old.injective
      (hX.trans (p.old_containedEmbedding h S.incident a).symm)
    have he₂ : P.prefixEmb T y = e b := p.old.injective
      (hY.trans (p.old_containedEmbedding h S.incident b).symm)
    have hVal₁ : x.val = (e a).val := by
      simpa only [prefixEmb,intervalEmb_val,Nat.zero_add] using congrArg Fin.val he₁
    have hVal₂ : y.val = (e b).val := by
      simpa only [prefixEmb,intervalEmb_val,Nat.zero_add] using congrArg Fin.val he₂
    have hX₁ := hAll a
    have hY₁ := hAll b
    have hx := x.isLt
    have hy := y.isLt
    exact (hxy.ne (Fin.ext (by omega))).elim
  · exact ht

lemma not_le_old_of_empty {P : ChainTerm} (hP : P.rightChain = [])
    {S : BasicShape} (p : Identification P.toShape S.toShape) : ¬p.newGraph ≤ p.oldGraph := by
  intro h
  obtain ⟨a,ha⟩ := S.incident S.toShape.left
  have he := p.containedEmbedding_adj h S.incident ha
  rw [p.containedEmbedding_left h S.incident] at he
  exact P.not_incident_right_of_empty hP ⟨_,he⟩

end ChainTerm

end LovaszTheta.Independent
