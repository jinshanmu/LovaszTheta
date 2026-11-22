module

public import LovaszTheta.TracePairing

/-!
# Label count and exceptional positions

Every used label has a first and a last occurrence. The number of
middle incidences above the mandatory one at each interior block
gives both the label-count penalty and the number of exceptional
positions.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l : ℕ}

/-- The trace positions between the first and last. -/
noncomputable def interiorPositions (l : ℕ) : Finset (Fin (l+2)) :=
  (univ.erase 0).erase (Fin.last (l+1))

lemma mem_interiorPositions {i : Fin (l+2)} :
    i ∈ interiorPositions l ↔ 0 < i.val ∧ i.val+1 < l+2 := by
  unfold interiorPositions
  simp only [mem_erase,mem_univ,and_true]
  have hi : i.val < l+2 := i.isLt
  have he : i = Fin.last (l+1) ↔ i.val = l+1 := Fin.ext_iff
  have h₀ : i = 0 ↔ i.val = 0 := Fin.ext_iff
  simp only [ne_eq,he,h₀]
  omega

lemma card_interiorPositions (l : ℕ) : (interiorPositions l).card = l := by
  unfold interiorPositions
  have hLast : Fin.last (l+1) ∈ (univ : Finset (Fin (l+2))).erase 0 := by
    apply mem_erase.mpr
    exact ⟨fun h ↦ by have h' := congrArg Fin.val h; simp at h',mem_univ _⟩
  rw [card_erase_of_mem hLast,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  omega

private lemma middleCount_eq_zero_of_notMem_interior (c : TraceBlocks V (l+2)) (i : Fin (l+2))
    (hi : i ∉ interiorPositions l) : c.middleCount i = 0 := by
  unfold middleCount
  apply card_eq_zero.mpr
  apply eq_empty_of_forall_notMem
  intro u hu
  obtain ⟨_,⟨j,hj,_⟩,k,hk,_⟩ := (c.mem_middleLabels_iff i u).mp hu
  exact hi (mem_interiorPositions.mpr
    ⟨by have : j.val < i.val := hj; omega,by have : i.val < k.val := hk; have := k.isLt; omega⟩)

private lemma middleCount_pos_of_mem_interior {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges)
    {i : Fin (l+2)} (hi : i ∈ interiorPositions l) : 0 < c.middleCount i := by
  have hI := mem_interiorPositions.mp hi
  rcases exists_middleBoundary h hI.1 hI.2 with hl | hr
  · exact card_pos.mpr ⟨_,hl⟩
  · exact card_pos.mpr ⟨_,hr⟩

/-- The extra middle-label incidences in the sharp trace count. -/
noncomputable def defect (c : TraceBlocks V (l+2)) : ℕ :=
  ∑ i ∈ interiorPositions l, (c.middleCount i-1)

/-- Positions that have two or more middle labels. -/
noncomputable def exceptionalPositions (c : TraceBlocks V (l+2)) : Finset (Fin (l+2)) :=
  univ.filter fun i ↦ ¬simplePosition c.block i

lemma mem_exceptionalPositions {c : TraceBlocks V (l+2)} {i : Fin (l+2)} :
    i ∈ c.exceptionalPositions ↔ 2 ≤ c.middleCount i := by
  unfold exceptionalPositions
  rw [Finset.mem_filter]
  simp only [mem_univ,true_and]
  change ¬c.middleCount i ≤ 1 ↔ 2 ≤ c.middleCount i
  omega

/-- There are at most t exceptional positions. -/
theorem card_exceptionalPositions_le (c : TraceBlocks V (l+2)) :
    c.exceptionalPositions.card ≤ c.defect := by
  have hSub : c.exceptionalPositions ⊆ interiorPositions l := by
    intro i hi
    by_contra hn
    have h := middleCount_eq_zero_of_notMem_interior c i hn
    exact (by decide : ¬(2 : ℕ) ≤ 0) ((mem_exceptionalPositions.mp hi).trans_eq h)
  calc
    _ = ∑ _ ∈ c.exceptionalPositions, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ c.exceptionalPositions, (c.middleCount i-1) := by
      apply sum_le_sum
      intro i hi
      have h := mem_exceptionalPositions.mp hi
      omega
    _ ≤ c.defect := sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ ↦ Nat.zero_le _)

lemma sum_middleCount_eq_defect {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) :
    (∑ i, c.middleCount i) = c.defect + l := by
  have he : (∑ i ∈ interiorPositions l, c.middleCount i) = ∑ i, c.middleCount i :=
    sum_subset (subset_univ _) (fun i _ hi ↦ middleCount_eq_zero_of_notMem_interior c i hi)
  have hCard : (∑ _ ∈ interiorPositions l, (1 : ℕ)) = l := by
    simp [card_interiorPositions]
  calc
    _ = ∑ i ∈ interiorPositions l, c.middleCount i := he.symm
    _ = c.defect + ∑ _ ∈ interiorPositions l, (1 : ℕ) := by
      rw [defect,← sum_add_distrib]
      exact sum_congr rfl fun i hi ↦ (Nat.sub_add_cancel (middleCount_pos_of_mem_interior h hi)).symm
    _ = _ := by rw [hCard]

private lemma card_occurrences_ge_two {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) (u : V)
    (hu : (occurrences (fun j ↦ (c.block j).vertices) u).Nonempty) :
    2 ≤ (occurrences (fun j ↦ (c.block j).vertices) u).card := by
  obtain ⟨i,hi⟩ := hu
  have hU : u ∈ (c.block i).vertices := (mem_filter.mp hi).2
  obtain ⟨v,he⟩ := ((c.block i).incident_iff_mem_vertices u).mpr hU
  obtain ⟨j,hji,hj⟩ := h i u v he
  have hJ : j ∈ occurrences (fun j ↦ (c.block j).vertices) u :=
    mem_filter.mpr ⟨mem_univ _,LabeledBlock.mem_vertices_of_adj hj⟩
  have hSub : ({j,i} : Finset (Fin (l+2))) ⊆ occurrences (fun j ↦ (c.block j).vertices) u := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact hJ
    · rw [mem_singleton.mp hk]
      exact hi
  exact (card_pair hji).ge.trans (card_le_card hSub)

/-- Exact accounting for the number of used labels in a contributing trace. -/
theorem card_usedLabels_defect [Fintype V] {c : TraceBlocks V (l+2)} (h : c.RepeatedEdges) :
    2*(usedLabels (fun j ↦ (c.block j).vertices)).card + (l+2) + c.defect =
      2 + ∑ i, ((c.block i).shape.additionalVertices+2) := by
  have hCount := sum_card_blocks (fun j ↦ (c.block j).vertices) (card_occurrences_ge_two h)
  change (∑ i, (c.block i).vertices.card) =
    2*(usedLabels (fun j ↦ (c.block j).vertices)).card + ∑ i, c.middleCount i at hCount
  have hV (i : Fin (l+2)) : (c.block i).vertices.card = (c.block i).shape.additionalVertices+2 := by
    simp only [LabeledBlock.vertices,card_map,card_univ,Fintype.card_fin]
  simp only [hV,sum_middleCount_eq_defect h] at hCount
  omega

end LovaszTheta.Independent.TraceBlocks
