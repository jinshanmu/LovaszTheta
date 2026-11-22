module

public import LovaszTheta.IdentificationProduct
public import LovaszTheta.EdgeSplit
public import LovaszTheta.RoughNorm

/-!
# Shared vertices that remain in a product

Isolated interior vertices are exactly the shared vertices that are
neither incident to a surviving edge nor retained as a boundary.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent.Identification

variable {P S : Shape} (p : Identification P S)

/-- The left boundary in the quotient before numbering. -/
def outputLeft : p.Vertex := p.old P.left

/-- The right boundary in the quotient before numbering. -/
def outputRight : p.Vertex := p.new S.right

lemma numbered_left : p.numbering p.outputLeft = p.shape.left := rfl

lemma numbered_right : p.numbering p.outputRight = p.shape.right := rfl

lemma numbered_adj {u v : p.Vertex} :
    p.shape.graph.Adj (p.numbering u) (p.numbering v) ↔ p.remaining.Adj u v := by
  change p.remaining.Adj (p.numbering.symm (p.numbering u)) (p.numbering.symm (p.numbering v)) ↔ _
  simp only [Equiv.symm_apply_apply]

/-- The quotient graph with its canonical numbering. -/
noncomputable def numberingIso : p.remaining ≃g p.shape.graph where
  toEquiv := p.numbering
  map_rel_iff' := fun {a b} ↦ p.numbered_adj (u := a) (v := b)

lemma reachable_iff :
    p.shape.graph.Reachable p.shape.left p.shape.right ↔
      p.remaining.Reachable p.outputLeft p.outputRight := by
  have he₁ (u : p.Vertex) : p.numberingIso.toHom u = p.numbering u := rfl
  have he₂ (a : Fin p.shape.vertexCount) : p.numberingIso.symm.toHom a = p.numbering.symm a := rfl
  constructor
  · intro hr
    have he := hr.map p.numberingIso.symm.toHom
    rw [he₂,he₂,← p.numbered_left,← p.numbered_right,Equiv.symm_apply_apply,Equiv.symm_apply_apply] at he
    exact he
  · intro hr
    have he := hr.map p.numberingIso.toHom
    rw [he₁,he₁,p.numbered_left,p.numbered_right] at he
    exact he

/-- Shared vertices that are incident to a surviving edge or remain as a boundary. -/
noncomputable def liveShared : Finset p.Vertex :=
  p.shared.filter fun u ↦ Incident p.remaining u ∨ u = p.outputLeft ∨ u = p.outputRight

lemma mem_liveShared {u : p.Vertex} :
    u ∈ p.liveShared ↔ u ∈ p.shared ∧
      (Incident p.remaining u ∨ u = p.outputLeft ∨ u = p.outputRight) :=
  mem_filter

lemma join_mem_shared : p.old P.right ∈ p.shared :=
  p.mem_shared.mpr ⟨⟨P.right,rfl⟩,⟨S.left,p.join⟩⟩

lemma mem_old_of_oldAdj {u v : p.Vertex} (h : p.oldGraph.Adj u v) : u ∈ Set.range p.old := by
  obtain ⟨a,_,_,ha,_⟩ := (SimpleGraph.map_adj p.old P.graph _ _).mp h
  exact ⟨a,ha⟩

lemma mem_new_of_newAdj {u v : p.Vertex} (h : p.newGraph.Adj u v) : u ∈ Set.range p.new := by
  obtain ⟨a,_,_,ha,_⟩ := (SimpleGraph.map_adj p.new S.graph _ _).mp h
  exact ⟨a,ha⟩

lemma oldAdj_remains_of_not_shared {u v : p.Vertex} (hu : u ∉ p.shared) (he : p.oldGraph.Adj u v) :
    p.remaining.Adj u v :=
  Or.inl ⟨he,fun hn ↦ hu (p.mem_shared.mpr ⟨p.mem_old_of_oldAdj he,p.mem_new_of_newAdj hn⟩)⟩

lemma newAdj_remains_of_not_shared {u v : p.Vertex} (hu : u ∉ p.shared) (he : p.newGraph.Adj u v) :
    p.remaining.Adj u v :=
  Or.inr ⟨he,fun hn ↦ hu (p.mem_shared.mpr ⟨p.mem_old_of_oldAdj hn,p.mem_new_of_newAdj he⟩)⟩

lemma shared_of_not_incident
    (hP : ∀ u, u ≠ P.left → u ≠ P.right → Incident P.graph u)
    (hS : ∀ u, Incident S.graph u)
    {u : p.Vertex} (hL : u ≠ p.outputLeft) (hR : u ≠ p.outputRight)
    (hIso : ¬Incident p.remaining u) : u ∈ p.shared := by
  by_contra h
  rcases p.vertex_in_factors u with ⟨a,rfl⟩ | ⟨b,rfl⟩
  · have hNe : a ≠ P.right := fun he ↦ h (he.symm ▸ p.join_mem_shared)
    obtain ⟨b,hb⟩ := hP a (fun he ↦ hL (congrArg p.old he)) hNe
    exact hIso ⟨_,p.oldAdj_remains_of_not_shared h (SimpleGraph.map_adj_apply.mpr hb)⟩
  · obtain ⟨a,ha⟩ := hS b
    exact hIso ⟨_,p.newAdj_remains_of_not_shared h (SimpleGraph.map_adj_apply.mpr ha)⟩

lemma mem_isolated_iff {u : p.Vertex} :
    p.numbering u ∈ p.shape.isolatedInterior ↔
      u ≠ p.outputLeft ∧ u ≠ p.outputRight ∧ ¬Incident p.remaining u := by
  unfold Shape.isolatedInterior
  simp only [mem_filter,mem_univ,true_and]
  rw [← p.numbered_left,← p.numbered_right,
    p.numbering.injective.ne_iff,p.numbering.injective.ne_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  constructor
  · rintro h ⟨v,hv⟩
    exact h (p.numbering v) (p.numbered_adj.mpr hv)
  · intro h v hv
    obtain ⟨w,rfl⟩ := p.numbering.surjective v
    exact h ⟨w,p.numbered_adj.mp hv⟩

/-- Isolated interior roles contribute exactly the shared vertices missing from the retained set. -/
theorem card_isolated_add_liveShared
    (hP : ∀ u, u ≠ P.left → u ≠ P.right → Incident P.graph u)
    (hS : ∀ u, Incident S.graph u) :
    p.shape.isolatedInterior.card + p.liveShared.card = p.shared.card := by
  let D := p.shared.filter fun u ↦ ¬(Incident p.remaining u ∨ u = p.outputLeft ∨ u = p.outputRight)
  have hD : D.map p.numbering.toEmbedding = p.shape.isolatedInterior := by
    ext a
    obtain ⟨u,rfl⟩ := p.numbering.surjective a
    rw [mem_map_equiv,Equiv.symm_apply_apply,p.mem_isolated_iff]
    rw [mem_filter]
    push Not
    exact ⟨fun h ↦ ⟨h.2.2.1,h.2.2.2,h.2.1⟩,
      fun h ↦ ⟨p.shared_of_not_incident hP hS h.1 h.2.1 h.2.2,h.2.2,h.1,h.2.1⟩⟩
  rw [← hD,card_map,add_comm]
  exact card_filter_add_card_filter_not (s := p.shared) _

/-- The power left by the rough estimate after the two normalizations. -/
theorem normalized_rough_exponent
    (hP : ∀ u, u ≠ P.left → u ≠ P.right → Incident P.graph u)
    (hS : ∀ u, Incident S.graph u) (extra : ℕ) :
    ((p.shape.vertexCount + p.shape.isolatedInterior.card - p.shape.boundaryIndicator : ℕ) : ℝ)/2 -
      ((P.vertexCount : ℝ)+S.vertexCount-2+extra)/2 =
      (2-(p.liveShared.card : ℝ)-p.shape.boundaryIndicator-extra)/2 := by
  have hInd : p.shape.boundaryIndicator ≤ 1 := by
    unfold Shape.boundaryIndicator
    split_ifs <;> omega
  have hV : 0 < p.shape.vertexCount := Nat.zero_lt_of_lt p.shape.left.isLt
  have hI : p.shape.boundaryIndicator ≤ p.shape.vertexCount+p.shape.isolatedInterior.card := by omega
  rw [Nat.cast_sub hI]
  push_cast
  have hQ := congrArg (fun n : ℕ ↦ (n : ℝ)) p.card_vertex_add_shared
  have hU := congrArg (fun n : ℕ ↦ (n : ℝ)) (p.card_isolated_add_liveShared hP hS)
  push_cast at hQ hU
  change (p.shape.vertexCount : ℝ) + (p.shared.card : ℝ) = _ at hQ
  linarith

/-- If the left boundary connects to the joining vertex in the old factor, it can
reach a live shared vertex along surviving edges. -/
theorem reachable_liveShared (h : P.graph.Reachable P.left P.right) :
    ∃ u ∈ p.liveShared, p.remaining.Reachable p.outputLeft u := by
  have hPath : p.oldGraph.Reachable p.outputLeft (p.old P.right) :=
    h.map (SimpleGraph.Embedding.map p.old P.graph).toHom
  rw [SimpleGraph.reachable_iff_reflTransGen] at hPath
  have hFind {w : p.Vertex} (hw : Relation.ReflTransGen p.oldGraph.Adj p.outputLeft w) :
      (∃ u ∈ p.liveShared, p.remaining.Reachable p.outputLeft u) ∨
        w ∉ p.shared ∧ p.remaining.Reachable p.outputLeft w := by
    induction hw with
    | refl =>
      by_cases hL : p.outputLeft ∈ p.shared
      · exact Or.inl ⟨_,p.mem_liveShared.mpr ⟨hL,Or.inr (Or.inl rfl)⟩,Reachable.refl _⟩
      · exact Or.inr ⟨hL,Reachable.refl _⟩
    | @tail a b hr he ih =>
      rcases ih with hFound | ⟨ha,hPath⟩
      · exact Or.inl hFound
      · have hEdge := p.oldAdj_remains_of_not_shared ha he
        have hReach := hPath.trans hEdge.reachable
        by_cases hb : b ∈ p.shared
        · exact Or.inl ⟨b,p.mem_liveShared.mpr ⟨hb,Or.inl ⟨a,hEdge.symm⟩⟩,hReach⟩
        · exact Or.inr ⟨hb,hReach⟩
  exact (hFind hPath).resolve_right fun hn ↦ hn.1 p.join_mem_shared

end LovaszTheta.Independent.Identification
