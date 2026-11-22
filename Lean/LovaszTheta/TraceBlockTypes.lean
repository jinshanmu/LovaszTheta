module

public import LovaszTheta.LabeledBlocks
public import LovaszTheta.TraceLabels
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Forward and return blocks in the trace

The repeated boundary edge puts a boundary label among the middle
occurrences. If it is the only such label, connectivity after
deleting it forces the rest of the block to have one time direction.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

/-- A cyclic trace sequence of injectively labeled basic blocks. -/
structure TraceBlocks (V : Type*) (l : ℕ) where
  /-- The successive block labelings. -/
  block : Fin l → LabeledBlock V
  stitch : ∀ i, (block i).right = (block (finRotate l i)).left

namespace TraceBlocks

variable {V : Type*} {l : ℕ}

/-- Every labeled edge in a contributing term has another occurrence. -/
def RepeatedEdges (c : TraceBlocks V l) : Prop :=
  ∀ i u v, (c.block i).graph.Adj u v → ∃ j, j ≠ i ∧ (c.block j).graph.Adj u v

/-- The label is present before the given block. -/
def Earlier (c : TraceBlocks V l) (i : Fin l) (u : V) : Prop :=
  ∃ j, j < i ∧ u ∈ (c.block j).vertices

/-- The label is present after the given block. -/
def Later (c : TraceBlocks V l) (i : Fin l) (u : V) : Prop :=
  ∃ j, i < j ∧ u ∈ (c.block j).vertices

/-- All labels with a previous occurrence are the left boundary. -/
def Forward (c : TraceBlocks V l) (i : Fin l) : Prop :=
  ∀ u, u ∈ (c.block i).vertices → c.Earlier i u → u = (c.block i).left

/-- All labels with a subsequent occurrence are the right boundary. -/
def Return (c : TraceBlocks V l) (i : Fin l) : Prop :=
  ∀ u, u ∈ (c.block i).vertices → c.Later i u → u = (c.block i).right

/-- The middle label count of a block. -/
noncomputable def middleCount (c : TraceBlocks V l) (i : Fin l) : ℕ :=
  (middleLabels (fun j ↦ (c.block j).vertices) i).card

lemma mem_middleLabels_iff (c : TraceBlocks V l) (i : Fin l) (u : V) :
    u ∈ middleLabels (fun j ↦ (c.block j).vertices) i ↔
      u ∈ (c.block i).vertices ∧ c.Earlier i u ∧ c.Later i u := by
  simp only [middleLabels,mem_filter,middle,occurrences,mem_univ,true_and,Earlier,Later]
  constructor
  · rintro ⟨hi,_,⟨j,hj,hji⟩,k,hk,hik⟩
    exact ⟨hi,⟨j,hji,hj⟩,k,hik,hk⟩
  · rintro ⟨hi,⟨j,hji,hj⟩,k,hik,hk⟩
    exact ⟨hi,hi,⟨j,hj,hji⟩,k,hk,hik⟩

lemma forward_first (c : TraceBlocks V l) {i : Fin l} (hi : i.val = 0) :
    c.Forward i := by
  rintro u _ ⟨j,hj,_⟩
  have h : j.val < i.val := hj
  omega

lemma return_last (c : TraceBlocks V l) {i : Fin l} (hi : i.val+1 = l) :
    c.Return i := by
  rintro u _ ⟨j,hj,_⟩
  have h : i.val < j.val := hj
  have h' := j.isLt
  omega

lemma edge_of_forward_not_earlier {c : TraceBlocks V l} {i j : Fin l} (hi : c.Forward i) (hj : j < i)
    {u v : V} (h : (c.block i).graph.Adj u v) : ¬(c.block j).graph.Adj u v := by
  intro he
  have hu := hi u (LabeledBlock.mem_vertices_of_adj h) ⟨j,hj,LabeledBlock.mem_vertices_of_adj he⟩
  have hv := hi v (LabeledBlock.mem_vertices_of_adj h.symm) ⟨j,hj,LabeledBlock.mem_vertices_of_adj he.symm⟩
  exact h.ne (hu.trans hv.symm)

lemma edge_of_return_not_later {c : TraceBlocks V l} {i j : Fin l} (hi : c.Return i) (hj : i < j)
    {u v : V} (h : (c.block i).graph.Adj u v) : ¬(c.block j).graph.Adj u v := by
  intro he
  have hu := hi u (LabeledBlock.mem_vertices_of_adj h) ⟨j,hj,LabeledBlock.mem_vertices_of_adj he⟩
  have hv := hi v (LabeledBlock.mem_vertices_of_adj h.symm) ⟨j,hj,LabeledBlock.mem_vertices_of_adj he.symm⟩
  exact h.ne (hu.trans hv.symm)

lemma earlier_left {c : TraceBlocks V (l+2)} {i : Fin (l+2)} (hi : 0 < i.val) :
    c.Earlier i (c.block i).left := by
  let j : Fin (l+2) := ⟨i.val-1,by have := i.isLt; omega⟩
  have hj : finRotate (l+2) j = i := by
    have h : i.val-1 < l+1 := by have := i.isLt; omega
    have he := finRotate_of_lt h
    change finRotate (l+2) j = _ at he
    exact he.trans (Fin.ext (by change i.val-1+1=i.val; omega))
  have hji : j < i := by
    change i.val - 1 < i.val
    omega
  have he := c.stitch j
  rw [hj] at he
  exact ⟨j,hji,he ▸ (c.block j).right_mem_vertices⟩

lemma later_right {c : TraceBlocks V (l+2)} {i : Fin (l+2)} (hi : i.val+1 < l+2) :
    c.Later i (c.block i).right := by
  refine ⟨finRotate (l+2) i,?_,?_⟩
  · have h := finRotate_of_lt (show i.val < l+1 by omega)
    change finRotate (l+2) i = _ at h
    rw [h]
    exact Nat.lt_succ_self _
  · rw [c.stitch i]
    exact (c.block _).left_mem_vertices

private lemma eq_of_middleCount_le_one {c : TraceBlocks V l} {i : Fin l} (hi : c.middleCount i ≤ 1)
    {u v : V} (hu : u ∈ middleLabels (fun j ↦ (c.block j).vertices) i)
    (hv : v ∈ middleLabels (fun j ↦ (c.block j).vertices) i) : u = v := by
  by_contra hne
  have h : ({u,v} : Finset V) ⊆ middleLabels (fun j ↦ (c.block j).vertices) i := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hu
    · rw [mem_singleton.mp hw]
      exact hv
  have hc := card_le_card h
  rw [card_pair hne] at hc
  unfold middleCount at hi
  omega

lemma exists_middleBoundary {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hi : 0 < i.val) (hj : i.val+1 < l+2) :
    (c.block i).left ∈ middleLabels (fun j ↦ (c.block j).vertices) i ∨
      (c.block i).right ∈ middleLabels (fun j ↦ (c.block j).vertices) i := by
  obtain ⟨k,hk,he⟩ := h i _ _ (c.block i).graph_adj_left_right
  rcases lt_or_gt_of_ne hk with hki | hik
  · exact Or.inr ((mem_middleLabels_iff c i _).mpr ⟨(c.block i).right_mem_vertices,
      ⟨k,hki,LabeledBlock.mem_vertices_of_adj he.symm⟩,later_right hj⟩)
  · exact Or.inl ((mem_middleLabels_iff c i _).mpr ⟨(c.block i).left_mem_vertices,
      earlier_left hi,⟨k,hik,LabeledBlock.mem_vertices_of_adj he⟩⟩)

private lemma forward_of_single_left {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hi : c.middleCount i ≤ 1) (hj : i.val+1 < l+2)
    (hLeft : (c.block i).left ∈ middleLabels (fun j ↦ (c.block j).vertices) i) : c.Forward i := by
  let b := c.block i
  have hNew : ¬c.Earlier i b.right := fun he ↦ b.left_ne_right
    (eq_of_middleCount_le_one hi hLeft ((mem_middleLabels_iff c i _).mpr ⟨b.right_mem_vertices,he,later_right hj⟩))
  have hE {u v : V} (e : b.graph.Adj u v) (hu : u ≠ b.left) (_ : v ≠ b.left)
      (he : c.Earlier i u) : c.Earlier i v := by
    have hNo : ¬c.Later i u := fun hl ↦ hu (eq_of_middleCount_le_one hi
      ((mem_middleLabels_iff c i _).mpr ⟨LabeledBlock.mem_vertices_of_adj e,he,hl⟩) hLeft)
    obtain ⟨k,hk,hEdge⟩ := h i u v e
    rcases lt_or_gt_of_ne hk with hki | hik
    · exact ⟨k,hki,LabeledBlock.mem_vertices_of_adj hEdge.symm⟩
    · exact (hNo ⟨k,hik,LabeledBlock.mem_vertices_of_adj hEdge⟩).elim
  intro u hu he
  by_contra hne
  exact hNew (LabeledBlock.prop_of_vertexDeletion b.left_mem_vertices hu b.right_mem_vertices hne
    b.left_ne_right.symm @hE he)

private lemma return_of_single_right {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hi : c.middleCount i ≤ 1) (hj : 0 < i.val)
    (hRight : (c.block i).right ∈ middleLabels (fun j ↦ (c.block j).vertices) i) : c.Return i := by
  let b := c.block i
  have hLast : ¬c.Later i b.left := fun he ↦ b.left_ne_right
    (eq_of_middleCount_le_one hi ((mem_middleLabels_iff c i _).mpr ⟨b.left_mem_vertices,earlier_left hj,he⟩) hRight)
  have hE {u v : V} (e : b.graph.Adj u v) (hu : u ≠ b.right) (_ : v ≠ b.right)
      (he : c.Later i u) : c.Later i v := by
    have hNo : ¬c.Earlier i u := fun hl ↦ hu (eq_of_middleCount_le_one hi
      ((mem_middleLabels_iff c i _).mpr ⟨LabeledBlock.mem_vertices_of_adj e,hl,he⟩) hRight)
    obtain ⟨k,hk,hEdge⟩ := h i u v e
    rcases lt_or_gt_of_ne hk with hki | hik
    · exact (hNo ⟨k,hki,LabeledBlock.mem_vertices_of_adj hEdge⟩).elim
    · exact ⟨k,hik,LabeledBlock.mem_vertices_of_adj hEdge.symm⟩
  intro u hu he
  by_contra hne
  exact hLast (LabeledBlock.prop_of_vertexDeletion b.right_mem_vertices hu b.left_mem_vertices hne
    b.left_ne_right @hE he)

/-- Every block with fewer than two middle labels is forward or return. -/
theorem forward_or_return {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hi : c.middleCount i ≤ 1) : c.Forward i ∨ c.Return i := by
  by_cases hFirst : i.val = 0
  · exact Or.inl (forward_first c hFirst)
  by_cases hLast : i.val+1 = l+2
  · exact Or.inr (return_last c hLast)
  have h₁ : 0 < i.val := Nat.pos_of_ne_zero hFirst
  have h₂ : i.val+1 < l+2 := by have := i.isLt; omega
  exact (exists_middleBoundary h h₁ h₂).imp
    (forward_of_single_left h hi h₂) (return_of_single_right h hi h₁)

end TraceBlocks

end LovaszTheta.Independent
