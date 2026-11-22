module

public import LovaszTheta.PrivatePairLabels

/-!
# Waiting pairs in the equality-pattern code

The previous block supplies the start of a return. Only one
waiting pair can contain that start. If a different waiting
pair contains the other exposed endpoint, the destination is
forced. Otherwise the next unmarked block is forward.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l : ℕ} {c : TraceBlocks V (l+2)}

/-- An exact pair with no intervening uses of internal labels. -/
def privatePair (c : TraceBlocks V (l+2)) (i j : Fin (l+2)) : Prop :=
  exactPair c.block i j ∧ ∀ u, ¬c.InterveningPrivateLabel i j u

/-- A private pair whose forward block has been read and whose return is pending. -/
def waitingPair (c : TraceBlocks V (l+2)) (k i j : Fin (l+2)) : Prop :=
  c.privatePair i j ∧ i < k ∧ k ≤ j

/-- An unmarked position is in a private pair. -/
theorem exists_privatePair_of_notMem_marked {i : Fin (l+2)} (hi : i ∉ c.markedPositions) :
    ∃ j, c.privatePair i j ∨ c.privatePair j i := by
  have hU : i ∉ c.unpairedPositions := fun h ↦ hi (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h))))
  obtain ⟨j,hj | hj⟩ := Classical.byContradiction
    (fun hn ↦ hU (c.mem_unpairedPositions.mpr hn))
  · refine ⟨j,Or.inl ⟨hj,fun u hu ↦ hi ?_⟩⟩
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
      (mem_image.mpr ⟨(i,j),c.mem_markedPairs.mpr ⟨hj,u,hu⟩,rfl⟩))))
  · refine ⟨j,Or.inr ⟨hj,fun u hu ↦ hi ?_⟩⟩
    exact mem_union.mpr (Or.inr (mem_image.mpr ⟨(j,i),c.mem_markedPairs.mpr ⟨hj,u,hu⟩,rfl⟩))

lemma not_forward_and_return (h : c.RepeatedEdges) {i : Fin (l+2)}
    (hf : c.Forward i) (hr : c.Return i) : False := by
  have he := (c.block i).graph_adj_left_right
  obtain ⟨j,hj,hJ⟩ := h i _ _ he
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · exact edge_of_forward_not_earlier hf hlt he hJ
  · exact edge_of_return_not_later hr hgt he hJ

/-- Membership in a private pair makes both positions unmarked. -/
theorem notMem_markedPositions_of_privatePair (h : c.RepeatedEdges)
    {i j : Fin (l+2)} (hp : c.privatePair i j) :
    i ∉ c.markedPositions ∧ j ∉ c.markedPositions := by
  have hType := forward_return_of_exactPair h hp.1
  have hMarkedI : i ∉ c.markedPairs.image Prod.fst := by
    rintro hi
    obtain ⟨⟨p,q⟩,hh,he⟩ := mem_image.mp hi
    change p = i at he
    subst p
    obtain ⟨hp',u,hu⟩ := c.mem_markedPairs.mp hh
    have heq := c.exactPair_right_unique hp.1 hp'
    exact hp.2 u (heq.symm ▸ hu)
  have hMarkedJ : j ∉ c.markedPairs.image Prod.snd := by
    rintro hj
    obtain ⟨⟨p,q⟩,hh,he⟩ := mem_image.mp hj
    change q = j at he
    subst q
    obtain ⟨hp',u,hu⟩ := c.mem_markedPairs.mp hh
    have heq := c.exactPair_left_unique hp.1 hp'
    exact hp.2 u (heq.symm ▸ hu)
  have hCrossI : i ∉ c.markedPairs.image Prod.snd := by
    rintro hi
    obtain ⟨⟨p,q⟩,hh,he⟩ := mem_image.mp hi
    change q = i at he
    subst q
    exact not_forward_and_return h hType.1 (forward_return_of_exactPair h (c.mem_markedPairs.mp hh).1).2
  have hCrossJ : j ∉ c.markedPairs.image Prod.fst := by
    rintro hj
    obtain ⟨⟨p,q⟩,hh,he⟩ := mem_image.mp hj
    change p = j at he
    subst p
    exact not_forward_and_return h (forward_return_of_exactPair h (c.mem_markedPairs.mp hh).1).1 hType.2
  constructor
  · intro hi
    rcases mem_union.mp hi with hu | hf
    · rcases mem_union.mp hu with he | hf
      · exact (c.mem_unpairedPositions.mp he) ⟨j,Or.inl hp.1⟩
      · exact hMarkedI hf
    · exact hCrossI hf
  · intro hj
    rcases mem_union.mp hj with hu | hf
    · rcases mem_union.mp hu with he | hf
      · exact (c.mem_unpairedPositions.mp he) ⟨i,Or.inr hp.1⟩
      · exact hCrossJ hf
    · exact hMarkedJ hf

/-- Only a previously exposed endpoint of the forward block can start its return. -/
theorem return_left_is_endpoint {i j : Fin (l+2)} (hp : c.privatePair i j) :
    (c.block j).left = (c.block i).left ∨ (c.block j).left = (c.block i).right := by
  let u := (c.block j).left
  have hPos : 0 < j.val := by have : i.val < j.val := hp.1.1; omega
  obtain ⟨p,hP,hS⟩ := c.exists_predecessor_stitch hPos
  have hU : u ∈ (c.block p).vertices := by
    change (c.block j).left ∈ _
    rw [← hS]
    exact (c.block p).right_mem_vertices
  have hI : i ≤ p := by have : i.val < j.val := hp.1.1; change i.val ≤ p.val; omega
  rcases lt_or_eq_of_le hI with hlt | hEq
  · by_contra! hn
    have hV : u ∈ (c.block i).vertices :=
      (LabeledBlock.vertices_eq_of_graph_eq hp.1.2.2.2.1).symm ▸ (c.block j).left_mem_vertices
    exact hp.2 u ⟨hV,hn.1,hn.2,p,hlt,(show p.val < j.val by omega),hU⟩
  · exact Or.inr (hS.symm.trans (congrArg (fun k ↦ (c.block k).right) hEq.symm))

/-- The starting label locates a unique pending pair. -/
theorem waitingPair_unique_of_return_left (h : c.RepeatedEdges) {i j p q : Fin (l+2)}
    (hp : c.privatePair i j) (hq : c.waitingPair j p q)
    (hEndpoint : (c.block j).left = (c.block p).left ∨ (c.block j).left = (c.block p).right) :
    p = i ∧ q = j := by
  have hU : (c.block j).left ∈ (c.block p).vertices := by
    rcases hEndpoint with hU | hU
    · exact hU.symm ▸ (c.block p).left_mem_vertices
    · exact hU.symm ▸ (c.block p).right_mem_vertices
  have hUq := (LabeledBlock.vertices_eq_of_graph_eq hq.1.1.2.2.2.1) ▸ hU
  rcases lt_or_eq_of_le hq.2.2 with hlt | hEq
  · have hr := (forward_return_of_exactPair h hp.1).2
    exact ((c.block j).left_ne_right (hr _ (c.block j).left_mem_vertices ⟨q,hlt,hUq⟩)).elim
  · subst q
    exact ⟨c.exactPair_left_unique hq.1.1 hp.1,rfl⟩

/-- The other previously exposed endpoint of the forward block. -/
noncomputable def otherEndpoint (b : LabeledBlock V) (start : V) : V :=
  if start = b.left then b.right else b.left

/-- A further waiting pair containing the other exposed endpoint forces the destination. -/
theorem return_right_eq_otherEndpoint_of_waiting (h : c.RepeatedEdges) {i j p q : Fin (l+2)}
    (hp : c.privatePair i j) (hq : c.waitingPair j p q) (hne : p ≠ i)
    (he : otherEndpoint (c.block i) (c.block j).left ∈ (c.block p).vertices) :
    (c.block j).right = otherEndpoint (c.block i) (c.block j).left := by
  let u := otherEndpoint (c.block i) (c.block j).left
  have hU : u ∈ (c.block i).vertices := by
    unfold u otherEndpoint
    split_ifs
    · exact (c.block i).right_mem_vertices
    · exact (c.block i).left_mem_vertices
  have hUj : u ∈ (c.block j).vertices := (LabeledBlock.vertices_eq_of_graph_eq hp.1.2.2.2.1) ▸ hU
  have hUq : u ∈ (c.block q).vertices := (LabeledBlock.vertices_eq_of_graph_eq hq.1.1.2.2.2.1) ▸ he
  have hJQ : j < q := lt_of_le_of_ne hq.2.2 (fun hEq ↦
    hne (c.exactPair_left_unique (hEq.symm ▸ hq.1.1) hp.1))
  exact ((forward_return_of_exactPair h hp.1).2 u hUj ⟨q,hJQ,hUq⟩).symm

/-- If no other pending pair contains the other endpoint, the next
block cannot be an unmarked return. -/
theorem no_next_privateReturn_of_no_waiting_other (h : c.RepeatedEdges)
    {i j k : Fin (l+2)} (hp : c.privatePair i j) (hk : k.val = j.val+1)
    (hNone : ∀ p q, c.waitingPair j p q → p ≠ i →
      otherEndpoint (c.block i) (c.block j).left ∉ (c.block p).vertices) :
    ¬∃ p, c.privatePair p k := by
  rintro ⟨p,hpk⟩
  have hPJ : p < j := by
    have hlt : p.val < k.val := hpk.1.1
    have hne : p ≠ j := fun he ↦ not_forward_and_return h
      (he ▸ (forward_return_of_exactPair h hpk.1).1) (forward_return_of_exactPair h hp.1).2
    exact lt_of_le_of_ne (show p.val ≤ j.val by omega) hne
  have hJK : j < k := by change j.val < k.val; omega
  have hRot : finRotate (l+2) j = k := by
    have he := finRotate_of_lt (show j.val < l+1 by have := k.isLt; omega)
    change finRotate (l+2) j = _ at he
    exact he.trans (Fin.ext hk.symm)
  have hS : (c.block j).right = (c.block k).left := (c.stitch j).trans
    (congrArg (fun r ↦ (c.block r).left) hRot)
  let u := (c.block j).right
  have hUp : u ∈ (c.block p).vertices := by
    change (c.block j).right ∈ _
    rw [hS]
    rcases return_left_is_endpoint hpk with h₁ | h₂
    · rw [h₁]; exact (c.block p).left_mem_vertices
    · rw [h₂]; exact (c.block p).right_mem_vertices
  have hPI : p ≠ i := fun he ↦ hJK.ne (c.exactPair_right_unique hp.1 (he ▸ hpk.1))
  have hU : u ≠ otherEndpoint (c.block i) (c.block j).left := fun he ↦
    hNone p k ⟨hpk,hPJ,hJK.le⟩ hPI (he ▸ hUp)
  have huNe : u ≠ (c.block j).left := (c.block j).left_ne_right.symm
  have hUo : u ≠ (c.block i).left ∧ u ≠ (c.block i).right := by
    rcases return_left_is_endpoint hp with hL | hR
    · refine ⟨fun he ↦ huNe (he.trans hL.symm),?_⟩
      simpa only [otherEndpoint,hL,ite_true] using hU
    · refine ⟨?_,fun he ↦ huNe (he.trans hR.symm)⟩
      simpa only [otherEndpoint,hR,ite_eq_right (c.block i).left_ne_right.symm] using hU
  have hUi : u ∈ (c.block i).vertices :=
    (LabeledBlock.vertices_eq_of_graph_eq hp.1.2.2.2.1).symm ▸ (c.block j).right_mem_vertices
  rcases lt_or_gt_of_ne hPI with hlt | hgt
  · exact hUo.1 ((forward_return_of_exactPair h hp.1).1 u hUi ⟨p,hlt,hUp⟩)
  · exact hp.2 u ⟨hUi,hUo.1,hUo.2,p,hgt,hPJ,hUp⟩

end TraceBlocks

end LovaszTheta.Independent
