module

public import LovaszTheta.GraphMatrices
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Label counts for colored graph-matrix trace terms

In a trace of a power of the matrix times its transpose, the copies are
indexed by a cyclic index and a Boolean orientation. Pairing at the
boundaries and repetition of each sign restrict the labels at each role.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {V : Type*}

/-- A family of injective labelings in the trace of a power of the matrix
times its transpose. The two orientations at a given index share a right
boundary, and consecutive indices share a left boundary. -/
structure ColoredTrace (α : Shape) (k : ℕ) (color : V → Fin α.vertexCount) where
  /-- Labeling of each oriented copy. -/
  labelling : Fin k × Bool → Fin α.vertexCount ↪ V
  /-- Every copy uses the same vertex colors. -/
  color_eq : ∀ i a, color (labelling i a) = a
  /-- A copy and the following transpose share the right boundary. -/
  right_eq : ∀ i, labelling (i, false) α.right = labelling (i, true) α.right
  /-- A transpose and the next copy share the left boundary. -/
  left_eq : ∀ i, labelling (i, true) α.left = labelling (finRotate k i, false) α.left
  /-- The independent sign at each labeled edge has even degree. -/
  even_edges : ∀ e : EdgeIndex V,
    Even ((univ.filter fun i ↦ e ∈ labelledEdges α (labelling i)).card)

variable {α : Shape} {k : ℕ} {color : V → Fin α.vertexCount}

/-- The set of labels in all copies of a fixed vertex role. -/
noncomputable def ColoredTrace.roleLabels (t : ColoredTrace α k color)
    (a : Fin α.vertexCount) : Finset V :=
  univ.image fun i ↦ t.labelling i a

/-- The set of labeled edges contributed by a fixed edge role. -/
noncomputable def ColoredTrace.roleEdges (t : ColoredTrace α k color)
    (e : α.graph.edgeSet) : Finset (EdgeIndex V) :=
  univ.image fun i ↦ edgeEmbedding α (t.labelling i) e

/-- The set of all labels in the trace. -/
noncomputable def ColoredTrace.labels (t : ColoredTrace α k color) : Finset V :=
  univ.biUnion t.roleLabels

private lemma card_image_le_of_repeat {ι β : Type*} [Fintype ι] [DecidableEq β] (f : ι → β) (k : ℕ)
    (hCard : Fintype.card ι = 2 * k)
    (hRepeat : ∀ i, ∃ j, j ≠ i ∧ f j = f i) :
    (univ.image f).card ≤ k := by
  have hc : 2 * (univ.image f).card ≤ Fintype.card ι := by
    rw [← card_univ, card_eq_sum_card_image f, mul_comm 2]
    rw [← sum_const_nat (f := fun _ ↦ 2) (fun _ _ ↦ rfl)]
    apply sum_le_sum
    intro b hb
    obtain ⟨i, _, rfl⟩ := mem_image.mp hb
    obtain ⟨j, hji, he⟩ := hRepeat i
    have hSub : {i, j} ⊆ univ.filter (fun l ↦ f l = f i) := by
      intro l hl
      simp only [mem_insert, mem_singleton] at hl
      rcases hl with rfl | rfl <;> simp [he]
    simpa [hji.symm] using card_le_card hSub
  omega

private lemma edge_eq_of_labelled_eq (t : ColoredTrace α k color) (i j : Fin k × Bool)
    (e e' : α.graph.edgeSet)
    (h : edgeEmbedding α (t.labelling i) e = edgeEmbedding α (t.labelling j) e') :
    e = e' := by
  have hv := congrArg (fun a : EdgeIndex V ↦ a.val.map color) h
  change ((e.val.map (t.labelling i)).map color) = (e'.val.map (t.labelling j)).map color at hv
  have hMap (i : Fin k × Bool) : color ∘ t.labelling i = id := funext (t.color_eq i)
  rw [Sym2.map_map, Sym2.map_map, hMap i, hMap j, Sym2.map_id] at hv
  exact Subtype.ext hv

/-- A labeled edge occurs in another copy of the same shape edge. -/
lemma ColoredTrace.exists_edge_repeat (t : ColoredTrace α k color) (i : Fin k × Bool)
    (e : α.graph.edgeSet) :
    ∃ j, j ≠ i ∧ edgeEmbedding α (t.labelling j) e = edgeEmbedding α (t.labelling i) e := by
  let b := edgeEmbedding α (t.labelling i) e
  let S := (univ : Finset (Fin k × Bool)).filter (fun j ↦ b ∈ labelledEdges α (t.labelling j))
  have hi : i ∈ S := mem_filter.mpr ⟨mem_univ _, mem_map.mpr ⟨e, mem_univ _, rfl⟩⟩
  have hEven : Even S.card := t.even_edges b
  have hCard : 2 ≤ S.card := by
    have hpos := card_pos.mpr ⟨i, hi⟩
    obtain ⟨m, hm⟩ := hEven
    omega
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < (S.erase i).card by
    rw [card_erase_of_mem hi]
    omega)
  have hjS := mem_erase.mp hj
  obtain ⟨e', _, he'⟩ := mem_map.mp (mem_filter.mp hjS.2).2
  have he : e' = e := edge_eq_of_labelled_eq t j i e' e he'
  subst e'
  exact ⟨j, hjS.1, he'⟩

lemma ColoredTrace.card_roleEdges_le (t : ColoredTrace α k color) (e : α.graph.edgeSet) :
    (t.roleEdges e).card ≤ k :=
  card_image_le_of_repeat (fun i ↦ edgeEmbedding α (t.labelling i) e) k
    (by simp [Fintype.card_prod, mul_comm])
    (fun i ↦ t.exists_edge_repeat i e)

/-- A nonisolated vertex role uses at most one label per pair of copies. -/
lemma ColoredTrace.card_roleLabels_le_of_adj (t : ColoredTrace α k color)
    {a b : Fin α.vertexCount} (hab : α.graph.Adj a b) :
    (t.roleLabels a).card ≤ k := by
  apply card_image_le_of_repeat _ _ (by simp [Fintype.card_prod, mul_comm])
  intro i
  let e : α.graph.edgeSet := ⟨s(a, b), hab⟩
  obtain ⟨j, hji, he⟩ := t.exists_edge_repeat i e
  have hv := congrArg Subtype.val he
  change s(t.labelling j a, t.labelling j b) = s(t.labelling i a, t.labelling i b) at hv
  rcases Sym2.eq_iff.mp hv with h | h
  · exact ⟨j, hji, h.1⟩
  · have hc := congrArg color h.1
    rw [t.color_eq, t.color_eq] at hc
    exact (hab.ne hc).elim

/-- The right boundary label is paired in the two orientations. -/
lemma ColoredTrace.card_rightLabels_le (t : ColoredTrace α k color) :
    (t.roleLabels α.right).card ≤ k := by
  apply card_image_le_of_repeat _ _ (by simp [Fintype.card_prod, mul_comm])
  rintro ⟨i, b⟩
  cases b
  · exact ⟨(i, true), by simp, (t.right_eq i).symm⟩
  · exact ⟨(i, false), by simp, t.right_eq i⟩

/-- The left boundary label is paired across consecutive cyclic indices. -/
lemma ColoredTrace.card_leftLabels_le (t : ColoredTrace α k color) :
    (t.roleLabels α.left).card ≤ k := by
  apply card_image_le_of_repeat _ _ (by simp [Fintype.card_prod, mul_comm])
  rintro ⟨i, b⟩
  cases b
  · refine ⟨((finRotate k).symm i, true), ?_, ?_⟩
    · intro h
      cases congrArg Prod.snd h
    · simpa only [Equiv.apply_symm_apply] using t.left_eq ((finRotate k).symm i)
  · refine ⟨(finRotate k i, false), ?_, (t.left_eq i).symm⟩
    intro h
    cases congrArg Prod.snd h

lemma ColoredTrace.card_roleLabels_le (t : ColoredTrace α k color) (a : Fin α.vertexCount) :
    (t.roleLabels a).card ≤ 2 * k := by
  unfold ColoredTrace.roleLabels
  exact card_image_le.trans (by simp [Fintype.card_prod, mul_comm])

/-- Isolated roles other than the two boundaries are charged twice in the
trace count. -/
noncomputable def Shape.isolatedInterior (α : Shape) : Finset (Fin α.vertexCount) :=
  univ.filter fun a ↦ a ≠ α.left ∧ a ≠ α.right ∧ ∀ b, ¬α.graph.Adj a b

private lemma ColoredTrace.card_roleLabels_le_of_not_isolatedInterior
    (t : ColoredTrace α k color) {a : Fin α.vertexCount} (ha : a ∉ α.isolatedInterior) :
    (t.roleLabels a).card ≤ k := by
  by_cases hl : a = α.left
  · subst a
    exact t.card_leftLabels_le
  by_cases hr : a = α.right
  · subst a
    exact t.card_rightLabels_le
  have hAdj : ∃ b, α.graph.Adj a b := by
    by_contra! h
    exact ha (mem_filter.mpr ⟨mem_univ _, hl, hr, h⟩)
  obtain ⟨b, hab⟩ := hAdj
  exact t.card_roleLabels_le_of_adj hab

/-- Sum of the role-wise bounds on a subset of the shape's vertices. -/
lemma ColoredTrace.sum_card_roleLabels_le (t : ColoredTrace α k color)
    (s : Finset (Fin α.vertexCount)) :
    (∑ a ∈ s, (t.roleLabels a).card) ≤ k * (s.card + (s ∩ α.isolatedInterior).card) := by
  calc
    _ ≤ ∑ a ∈ s, (k + if a ∈ α.isolatedInterior then k else 0) := by
      apply sum_le_sum
      intro a ha
      by_cases h : a ∈ α.isolatedInterior
      · simpa only [h, ite_true, two_mul] using t.card_roleLabels_le a
      · simpa only [h, ite_false, add_zero] using t.card_roleLabels_le_of_not_isolatedInterior h
    _ = _ := by
      rw [sum_add_distrib, sum_ite_mem, sum_const, sum_const]
      simp [mul_add, mul_comm]

/-- The colored trace bound prior to sharpening it along a boundary path. -/
theorem ColoredTrace.card_labels_le (t : ColoredTrace α k color) :
    t.labels.card ≤ k * (α.vertexCount + α.isolatedInterior.card) := by
  unfold ColoredTrace.labels
  exact card_biUnion_le.trans (by simpa using t.sum_card_roleLabels_le univ)

end LovaszTheta.Independent
