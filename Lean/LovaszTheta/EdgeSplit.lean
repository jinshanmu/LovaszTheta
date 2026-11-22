module

public import LovaszTheta.GraphMatrices
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Splitting the edges of a basic block

Deleting a vertex leaves the block connected. When its edges
are split into two nonempty sets, each component of either
part therefore contains at least two mixed vertices.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {V : Type*}

/-- Each induced graph obtained by deleting one vertex is preconnected. -/
def VertexDeletionConnected (G : SimpleGraph V) : Prop :=
  ∀ x : V, (G.induce {v | v ≠ x}).Preconnected

/-- A vertex incident to an edge of the given color. -/
def Incident (R : SimpleGraph V) (v : V) : Prop := ∃ u, R.Adj v u

/-- A vertex incident to both colors. -/
def Mixed (R B : SimpleGraph V) (v : V) : Prop := Incident R v ∧ Incident B v

private lemma incident_of_reachable {R : SimpleGraph V} {u v : V}
    (hu : Incident R u) (h : R.Reachable u v) : Incident R v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hAdj _ => exact ⟨_,hAdj.symm⟩

private lemma reachable_inside_component_of_avoid_mixed {G R B : SimpleGraph V}
    (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    {r x : V} (hr : Incident R r) (hOnly : ∀ v, R.Reachable r v → Mixed R B v → v = x)
    {u v : {w : V // w ≠ x}} (h : (G.induce {w | w ≠ x}).Reachable u v)
    (hu : R.Reachable r u.val) : R.Reachable r v.val := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail hPath hAdj ih =>
    rename_i a b
    have hReach := ih
    have hEdge : G.Adj a.val b.val := hAdj
    rcases hPartition hEdge with hR | hB
    · exact hReach.trans hR.reachable
    · exact (a.property (hOnly a.val hReach ⟨incident_of_reachable hr hReach,⟨b.val,hB⟩⟩)).elim

/-- Every nontrivial component of the red part of an edge split
meets the blue part at two distinct vertices. -/
theorem exists_two_mixed_of_edgeSplit {G R B : SimpleGraph V} (hG : VertexDeletionConnected G)
    (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    {r : V} (hr : Incident R r) (hB : ∃ v, Incident B v) :
    ∃ a b : V, a ≠ b ∧ R.Reachable r a ∧ R.Reachable r b ∧ Mixed R B a ∧ Mixed R B b := by
  by_contra hNo
  have hUnique (a b : V) (ha : R.Reachable r a) (hb : R.Reachable r b)
      (hma : Mixed R B a) (hmb : Mixed R B b) : a = b :=
    Classical.byContradiction (fun hne ↦ hNo ⟨a,b,hne,ha,hb,hma,hmb⟩)
  have hx : ∃ x : V, (∀ v, R.Reachable r v → Mixed R B v → v = x) ∧ R.Reachable r x := by
    by_cases h : ∃ x, R.Reachable r x ∧ Mixed R B x
    · obtain ⟨x,hR,hMixed⟩ := h
      exact ⟨x,fun v hv hm ↦ hUnique v x hv hR hm hMixed,hR⟩
    · exact ⟨r,fun v hv hm ↦ (h ⟨v,hv,hm⟩).elim,SimpleGraph.Reachable.refl _⟩
  obtain ⟨x,hOnly,hRx⟩ := hx
  obtain ⟨b,c,hbc⟩ := hB
  have hOut : ∃ v : V, ¬R.Reachable r v := by
    by_cases hb : R.Reachable r b
    · refine ⟨c,fun hc ↦ hbc.ne ?_⟩
      exact hUnique b c hb hc ⟨incident_of_reachable hr hb,⟨c,hbc⟩⟩
        ⟨incident_of_reachable hr hc,⟨b,hbc.symm⟩⟩
    · exact ⟨b,hb⟩
  obtain ⟨w,hw⟩ := hOut
  have hwx : w ≠ x := fun he ↦ hw (he.symm ▸ hRx)
  obtain ⟨a0,hra⟩ := hr
  have ha : ∃ v : V, v ≠ x ∧ R.Reachable r v := by
    by_cases he : r = x
    · exact ⟨a0,fun h ↦ hra.ne (he.trans h.symm),hra.reachable⟩
    · exact ⟨r,he,SimpleGraph.Reachable.refl _⟩
  obtain ⟨a,hax,ha⟩ := ha
  exact hw (reachable_inside_component_of_avoid_mixed hPartition ⟨a0,hra⟩ hOnly (hG x ⟨a,hax⟩ ⟨w,hwx⟩) ha)

/-- If the two colors meet at just two vertices, each color is
connected on its own incident vertices. -/
theorem reachable_of_edgeSplit_card_mixed_le_two [Fintype V] {G R B : SimpleGraph V}
    (hG : VertexDeletionConnected G)
    (hPartition : ∀ {u v}, G.Adj u v → R.Adj u v ∨ B.Adj u v)
    (hB : ∃ v, Incident B v) (hCard : (univ.filter (Mixed R B)).card ≤ 2)
    {u v : V} (hu : Incident R u) (hv : Incident R v) : R.Reachable u v := by
  obtain ⟨a,b,hab,hua,hub,hma,hmb⟩ := exists_two_mixed_of_edgeSplit hG hPartition hu hB
  obtain ⟨c,_,_,hvc,_,hmc,_⟩ := exists_two_mixed_of_edgeSplit hG hPartition hv hB
  have hSubset : ({a,b} : Finset V) ⊆ univ.filter (Mixed R B) := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _,hma⟩
    · exact mem_filter.mpr ⟨mem_univ _,hmb⟩
  have hSet : ({a,b} : Finset V) = univ.filter (Mixed R B) :=
    eq_of_subset_of_card_le hSubset (by simpa [card_pair hab] using hCard)
  have hc : c = a ∨ c = b := by
    have h : c ∈ ({a,b} : Finset V) := by rw [hSet]; exact mem_filter.mpr ⟨mem_univ c,hmc⟩
    simpa only [mem_insert,mem_singleton] using h
  rcases hc with rfl | rfl
  · exact hua.trans hvc.symm
  · exact hub.trans hvc.symm

end LovaszTheta.Independent
