module

public import LovaszTheta.RoughCounting
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Counting the labels along a boundary path

The images of a path joining the shape's boundaries concatenate in
trace order. The resulting closed walk uses at most one new vertex per
distinct edge, besides its starting point.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

private lemma card_walkSupport_le {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.toFinset.card ≤ p.edges.toFinset.card + 1 := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.support_cons, Walk.edges_cons, List.toFinset_cons]
    by_cases he : s(u, v) ∈ p.edges.toFinset
    · have hu : u ∈ p.support.toFinset := List.mem_toFinset.mpr
        (p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp he))
      simpa only [insert_eq_of_mem he, insert_eq_of_mem hu] using ih
    · rw [card_insert_of_notMem he]
      exact (card_insert_le _ _).trans (by omega)

private lemma exists_joinedWalk {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (a : Fin (k + 1) → V) (p : ∀ i : Fin k, G.Walk (a i.castSucc) (a i.succ)) :
    ∃ q : G.Walk (a 0) (a (Fin.last k)),
      (∀ i, (p i).support ⊆ q.support) ∧ (∀ e ∈ q.edges, ∃ i, e ∈ (p i).edges) := by
  induction k with
  | zero =>
    refine ⟨.nil, fun i ↦ i.elim0, ?_⟩
    simp
  | succ k ih =>
    let b (i : Fin (k + 1)) := a i.succ
    let tail (i : Fin k) : G.Walk (b i.castSucc) (b i.succ) := p i.succ
    obtain ⟨q, hqSupport, hqEdges⟩ := ih b tail
    let head := (p (0 : Fin (k+1))).copy (congrArg a Fin.castSucc_zero) rfl
    refine ⟨head.append q, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · intro x hx
        apply (Walk.mem_support_append_iff _ _).mpr
        exact Or.inl (by simpa only [head, Walk.support_copy] using hx)
      intro i x hx
      exact (Walk.mem_support_append_iff _ _).mpr (.inr (hqSupport i hx))
    · intro e he
      change e ∈ (head.append q).edges at he
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact ⟨0, by simpa only [head, Walk.edges_copy] using he⟩
      · obtain ⟨i, hi⟩ := hqEdges e he
        exact ⟨i.succ, hi⟩

/-- Closing a tuple of vertices by repeating its first vertex implements the
cyclic successor on all successive pairs. -/
lemma snoc_first_succ {V : Type*} {k : ℕ} (a : Fin (k+1) → V) (i : Fin (k+1)) :
    Fin.snoc (α := fun _ ↦ V) a (a 0) i.succ = a (finRotate (k+1) i) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [show j.castSucc.succ = j.succ.castSucc from rfl, Fin.snoc_castSucc]
    congr 1
    exact (finRotate_of_lt j.isLt).symm
  · rw [show (Fin.last k).succ = Fin.last (k+1) from rfl, Fin.snoc_last, finRotate_last]

variable {V : Type*} {α : Shape} {k : ℕ} {color : V → Fin α.vertexCount}

private abbrev labelledPathHom (t : ColoredTrace α k color) (i : Fin k × Bool) :
    α.graph →g (⊤ : SimpleGraph V) where
  toFun := t.labelling i
  map_rel' := fun h ↦ (t.labelling i).injective.ne h.ne

private def pairedWalk (t : ColoredTrace α k color) (p : α.graph.Walk α.left α.right)
    (i : Fin k) :
    (⊤ : SimpleGraph V).Walk (t.labelling (i, false) α.left)
      (t.labelling (finRotate k i, false) α.left) :=
  (p.map (labelledPathHom t (i, false))).append
    ((p.map (labelledPathHom t (i, true))).reverse.copy (t.right_eq i).symm (t.left_eq i))

private lemma mem_support_pairedWalk (t : ColoredTrace α k color)
    (p : α.graph.Walk α.left α.right) (i : Fin k) (b : Bool)
    {a : Fin α.vertexCount} (ha : a ∈ p.support) :
    t.labelling (i, b) a ∈ (pairedWalk t p i).support := by
  unfold pairedWalk
  rw [Walk.mem_support_append_iff, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
    Walk.support_map, Walk.support_map]
  cases b
  · exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)

private lemma mem_edges_pairedWalk (t : ColoredTrace α k color)
    (p : α.graph.Walk α.left α.right) (i : Fin k) {e : Sym2 V}
    (he : e ∈ (pairedWalk t p i).edges) :
    ∃ (b : Bool) (e' : α.graph.edgeSet), e'.val ∈ p.edges ∧
      (edgeEmbedding α (t.labelling (i, b)) e').val = e := by
  unfold pairedWalk at he
  rw [Walk.edges_append, List.mem_append, Walk.edges_copy, Walk.edges_reverse, List.mem_reverse,
    Walk.edges_map, Walk.edges_map] at he
  rcases he with he | he
  · obtain ⟨e', he', heq⟩ := List.mem_map.mp he
    exact ⟨false, ⟨e', p.edges_subset_edgeSet he'⟩, he', heq⟩
  · obtain ⟨e', he', heq⟩ := List.mem_map.mp he
    exact ⟨true, ⟨e', p.edges_subset_edgeSet he'⟩, he', heq⟩

private lemma exists_closedWalk_of_path {k : ℕ} {color : V → Fin α.vertexCount}
    (t : ColoredTrace α (k+1) color) (p : α.graph.Walk α.left α.right) :
    ∃ (a : V) (q : (⊤ : SimpleGraph V).Walk a a),
      (∀ j : Fin (k+1) × Bool, ∀ x ∈ p.support, t.labelling j x ∈ q.support) ∧
      ∀ e ∈ q.edges, ∃ (j : Fin (k+1) × Bool) (e' : α.graph.edgeSet), e'.val ∈ p.edges ∧
        (edgeEmbedding α (t.labelling j) e').val = e := by
  let a (i : Fin (k+1)) := t.labelling (i, false) α.left
  let vertices := Fin.snoc (α := fun _ ↦ V) a (a 0)
  have hStart (i : Fin (k+1)) : a i = vertices i.castSucc := by simp [vertices]
  let q (i : Fin (k+1)) : (⊤ : SimpleGraph V).Walk (vertices i.castSucc) (vertices i.succ) :=
    (pairedWalk t p i).copy (hStart i) (snoc_first_succ a i).symm
  obtain ⟨w, hwSupport, hwEdges⟩ := exists_joinedWalk vertices q
  have hEnd : vertices (Fin.last (k+1)) = vertices 0 := by simp [vertices]
  refine ⟨vertices 0, w.copy rfl hEnd, ?_, ?_⟩
  · rintro ⟨i, b⟩ x hx
    simp only [Walk.support_copy]
    apply hwSupport i
    simpa only [q, Walk.support_copy] using mem_support_pairedWalk t p i b hx
  · intro e he
    simp only [Walk.edges_copy] at he
    obtain ⟨i, hi⟩ := hwEdges e he
    have hi' : e ∈ (pairedWalk t p i).edges := by simpa only [q, Walk.edges_copy] using hi
    obtain ⟨b, e', he', heq⟩ := mem_edges_pairedWalk t p i hi'
    exact ⟨(i, b), e', he', heq⟩

private lemma ColoredTrace.card_labels_on_path_le {k : ℕ}
    (t : ColoredTrace α (k+1) color) (p : α.graph.Walk α.left α.right) :
    (p.support.toFinset.biUnion t.roleLabels).card ≤ (k+1) * p.length + 1 := by
  obtain ⟨_, w, hwSupport, hwEdges⟩ := exists_closedWalk_of_path t p
  let E := (univ : Finset α.graph.edgeSet).filter (fun e ↦ e.val ∈ p.edges)
  let F := E.biUnion (fun e ↦ (t.roleEdges e).image Subtype.val)
  have hVertex : p.support.toFinset.biUnion t.roleLabels ⊆ w.support.toFinset := by
    intro x hx
    obtain ⟨a, ha, hx⟩ := mem_biUnion.mp hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact List.mem_toFinset.mpr (hwSupport i a (List.mem_toFinset.mp ha))
  have hEdge : w.edges.toFinset ⊆ F := by
    intro e he
    obtain ⟨j, e', hEp, heq⟩ := hwEdges e (List.mem_toFinset.mp he)
    exact mem_biUnion.mpr ⟨e', mem_filter.mpr ⟨mem_univ _, hEp⟩,
      mem_image.mpr ⟨edgeEmbedding α (t.labelling j) e', mem_image_of_mem _ (mem_univ j), heq⟩⟩
  have hE : E.card ≤ p.length := by
    have hCard := card_le_card_of_injOn (s := E) (t := p.edges.toFinset) Subtype.val
      (fun e he ↦ List.mem_toFinset.mpr (mem_filter.mp he).2) Subtype.val_injective.injOn
    exact hCard.trans (by simpa only [Walk.length_edges] using p.edges.toFinset_card_le)
  have hF : F.card ≤ (k+1) * p.length := by
    calc
      _ ≤ ∑ e ∈ E, ((t.roleEdges e).image Subtype.val).card := card_biUnion_le
      _ ≤ ∑ _e ∈ E, (k+1) := sum_le_sum fun e _ ↦ card_image_le.trans (t.card_roleEdges_le e)
      _ = (k+1) * E.card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hE
  exact (card_le_card hVertex).trans ((card_walkSupport_le w).trans
    (Nat.add_le_add_right ((card_le_card hEdge).trans hF) _))

/-- The boundary path replaces the role-wise bound by one on all its labels
together. A length-zero path also covers coincident boundaries. -/
theorem ColoredTrace.card_labels_le_of_connected (t : ColoredTrace α k color)
    (hk : 0 < k) (hc : α.graph.Reachable α.left α.right) :
    t.labels.card ≤ k * (α.vertexCount + α.isolatedInterior.card - 1) + 1 := by
  obtain ⟨p, hp⟩ := hc.exists_isPath
  let S := p.support.toFinset
  have hS : S.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  have hRest : Sᶜ.card + (p.length + 1) = α.vertexCount := by
    simpa only [hS, Fintype.card_fin] using Finset.card_compl_add_card S
  have hIso : Sᶜ ∩ α.isolatedInterior = α.isolatedInterior := by
    apply inter_eq_right.mpr
    intro a ha
    obtain ⟨_, hal, _, hi⟩ := mem_filter.mp ha
    apply mem_compl.mpr
    intro haS
    have hNil := p.nil_of_isIsolated_of_mem_support hi (List.mem_toFinset.mp haS)
    have haSupport := List.mem_toFinset.mp haS
    rw [Walk.nil_iff_support_eq.mp hNil] at haSupport
    exact hal (List.mem_singleton.mp haSupport)
  have hPart : t.labels = S.biUnion t.roleLabels ∪ Sᶜ.biUnion t.roleLabels := by
    rw [← union_biUnion, Finset.union_compl, ColoredTrace.labels]
  have hPath : (S.biUnion t.roleLabels).card ≤ k * p.length + 1 := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact t.card_labels_on_path_le p
  rw [hPart]
  calc
    _ ≤ (S.biUnion t.roleLabels).card + (Sᶜ.biUnion t.roleLabels).card := card_union_le _ _
    _ ≤ k * p.length + 1 + k * (Sᶜ.card + α.isolatedInterior.card) := by
      apply add_le_add hPath (card_biUnion_le.trans _)
      simpa only [hIso] using t.sum_card_roleLabels_le Sᶜ
    _ = _ := by
      have h := show p.length + (Sᶜ.card + α.isolatedInterior.card) =
          α.vertexCount + α.isolatedInterior.card - 1 by omega
      rw [add_right_comm, ← Nat.mul_add, h]

end LovaszTheta.Independent
