module

public import LovaszTheta.CycleDeletion

/-!
# Basic block shapes

In their oriented cycle coordinates the boundaries are zero and
one. The spanning cycle is contained in the graph and the
edges have no alternating endpoints.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

/-- No two edges have strictly alternating endpoints in the cycle order. -/
def Noncrossing {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ {a u b v : Fin N}, a < u → u < b → b < v → G.Adj a b → ¬G.Adj u v

/-- The single edge or a cycle with noncrossing chords,
presented in the orientation from the left boundary to the right. -/
structure BasicShape where
  /-- The number of vertices is two plus this number. -/
  additionalVertices : ℕ
  /-- The graph in cycle order. -/
  graph : SimpleGraph (Fin (additionalVertices+2))
  cycle_le : cycleGraph (additionalVertices+2) ≤ graph
  noncrossing : Noncrossing graph

namespace BasicShape

/-- The corresponding shape with its ordered boundaries. -/
def toShape (T : BasicShape) : Shape :=
  ⟨T.additionalVertices+2,T.graph,0,1⟩

/-- All basic shapes remain connected after deleting a vertex. -/
theorem vertexDeletionConnected (T : BasicShape) : VertexDeletionConnected T.graph := by
  intro d
  exact (vertexDeletionConnected_cycleGraph T.additionalVertices d).mono (fun _ _ h ↦ T.cycle_le h)

lemma toShape_left_adj_right (T : BasicShape) : T.toShape.graph.Adj T.toShape.left T.toShape.right := by
  apply T.cycle_le
  apply cycleGraph_adj.mpr
  exact Or.inr (sub_zero 1)

end BasicShape

private lemma exists_interior_of_chord {n : ℕ} {a b : Fin (n+2)}
    (hab : a < b) (h : ¬(cycleGraph (n+2)).Adj a b) : ∃ u, a < u ∧ u < b := by
  have hGap : a.val+1 < b.val := by
    by_contra hh
    have he : b.val-a.val = 1 := by
      have hlt : a.val < b.val := hab
      omega
    exact h (cycleGraph_adj'.mpr (Or.inr ((Fin.sub_val_of_le hab.le).trans he)))
  exact ⟨⟨a.val+1,hGap.trans b.isLt⟩,by change a.val < a.val+1; omega,hGap⟩

private lemma exists_exterior_of_chord {n : ℕ} {a b : Fin (n+2)}
    (h : ¬(cycleGraph (n+2)).Adj a b) : ∃ u, u < a ∨ b < u := by
  by_cases ha : a = 0
  · have hb : b ≠ Fin.last (n+1) := by
      intro he
      apply h
      rw [ha,he]
      apply cycleGraph_adj'.mpr
      exact Or.inl (by simp)
    exact ⟨Fin.last (n+1),Or.inr (lt_of_le_of_ne (Fin.le_last b) hb)⟩
  · exact ⟨0,Or.inl (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha))⟩

private lemma not_adj_across_chord {N : ℕ} {G : SimpleGraph (Fin N)} (hG : Noncrossing G)
    {a b u v : Fin N} (hChord : G.Adj a b) (hau : a < u) (hub : u < b)
    (hv : v < a ∨ b < v) : ¬G.Adj u v := by
  rcases hv with hv | hv
  · intro he
    exact hG hv hau hub he.symm hChord
  · exact hG hau hub hv hChord

private lemma not_preconnected_remove_ordered_chord {n : ℕ} {G : SimpleGraph (Fin (n+2))}
    (hG : Noncrossing G) {a b : Fin (n+2)} (hab : a < b)
    (hAdj : G.Adj a b) (hn : ¬(cycleGraph (n+2)).Adj a b) :
    ¬(G.induce {v | v ≠ a ∧ v ≠ b}).Preconnected := by
  obtain ⟨u,ha,hb⟩ := exists_interior_of_chord hab hn
  obtain ⟨v,hout⟩ := exists_exterior_of_chord hn
  have hV : v ≠ a ∧ v ≠ b := by
    rcases hout with h | h
    · exact ⟨h.ne,(h.trans hab).ne⟩
    · exact ⟨(hab.trans h).ne',h.ne'⟩
  intro hCon
  have h := hCon ⟨u,ha.ne',hb.ne⟩ ⟨v,hV⟩
  rw [reachable_iff_reflTransGen] at h
  have hStay {w : {w // w ≠ a ∧ w ≠ b}}
      (h : Relation.ReflTransGen (G.induce {v | v ≠ a ∧ v ≠ b}).Adj ⟨u,ha.ne',hb.ne⟩ w) :
      a < w.val ∧ w.val < b := by
    induction h with
    | refl => exact ⟨ha,hb⟩
    | tail hR he ih =>
      rename_i p q
      have hAdj' : G.Adj p.val q.val := he
      have hNo : ¬(q.val < a ∨ b < q.val) :=
        fun hv ↦ not_adj_across_chord hG hAdj ih.1 ih.2 hv hAdj'
      exact ⟨lt_of_le_of_ne (le_of_not_gt (fun h ↦ hNo (Or.inl h))) q.property.1.symm,
        lt_of_le_of_ne (le_of_not_gt (fun h ↦ hNo (Or.inr h))) q.property.2⟩
  have hv := hStay h
  exact hout.elim (fun hh ↦ (not_lt_of_ge hv.1.le) hh) (fun hh ↦ (not_lt_of_ge hv.2.le) hh)

/-- The endpoints of a chord separate the interiors of its two arcs. -/
theorem not_preconnected_remove_chord {n : ℕ} {G : SimpleGraph (Fin (n+2))}
    (hG : Noncrossing G) {a b : Fin (n+2)}
    (hAdj : G.Adj a b) (hn : ¬(cycleGraph (n+2)).Adj a b) :
    ¬(G.induce {v | v ≠ a ∧ v ≠ b}).Preconnected := by
  rcases lt_or_gt_of_ne hAdj.ne with h | h
  · exact not_preconnected_remove_ordered_chord hG h hAdj hn
  · have hSet : {v | v ≠ a ∧ v ≠ b} = {v | v ≠ b ∧ v ≠ a} := by ext; exact and_comm
    rw [hSet]
    exact not_preconnected_remove_ordered_chord hG h hAdj.symm (fun he ↦ hn he.symm)

/-- A spanning cycle cannot traverse a chord of a noncrossing graph. -/
theorem cycle_adj_of_spanning_cycle {n : ℕ} {G : SimpleGraph (Fin (n+2))}
    (hG : Noncrossing G) (e : Equiv.Perm (Fin (n+2)))
    (hE : ∀ {u v}, (cycleGraph (n+2)).Adj u v → G.Adj (e u) (e v))
    {a b : Fin (n+2)} (h : (cycleGraph (n+2)).Adj a b) :
    (cycleGraph (n+2)).Adj (e a) (e b) := by
  by_contra hn
  let F : (cycleGraph (n+2)).induce {v | v ≠ a ∧ v ≠ b} →g
      G.induce {v | v ≠ e a ∧ v ≠ e b} :=
    { toFun := fun v ↦ ⟨e v.val,⟨e.injective.ne v.property.1,e.injective.ne v.property.2⟩⟩
      map_rel' := fun he ↦ hE he }
  have hSurj : Function.Surjective F := by
    rintro ⟨v,hv⟩
    refine ⟨⟨e.symm v,⟨fun he ↦ hv.1 ((e.symm_apply_eq).mp he),fun he ↦ hv.2 ((e.symm_apply_eq).mp he)⟩⟩,
      Subtype.ext (e.apply_symm_apply _)⟩
  exact not_preconnected_remove_chord hG (hE h) hn ((preconnected_cycleGraph_remove_adjacent h).map F hSurj)

end LovaszTheta.Independent
