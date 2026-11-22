module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic

/-!
# Counting labels between their first and last trace occurrences

The sharp moment count charges a half at the first and last occurrence
of each label. Equivalently, the total number of incidences is twice
the number of distinct labels plus the number of middle incidences.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

/-- Occurrences of a label in a sequence of sets of labels. -/
noncomputable def occurrences {I V : Type*} [Fintype I]
    (blocks : I → Finset V) (v : V) : Finset I :=
  univ.filter (fun i ↦ v ∈ blocks i)

/-- The incidences in a finite ordered set excluding its first and last elements. -/
noncomputable def middle {I : Type*} [LinearOrder I] (s : Finset I) : Finset I :=
  s.filter fun i ↦ (∃ l ∈ s, l < i) ∧ ∃ r ∈ s, i < r

private lemma middle_eq_erase {I : Type*} [LinearOrder I] {s : Finset I} (hs : s.Nonempty) :
    middle s = (s.erase (s.min' hs)).erase (s.max' hs) := by
  ext i
  simp only [middle, mem_filter, mem_erase]
  constructor
  · rintro ⟨hi, ⟨l, hl, hli⟩, r, hr, hir⟩
    exact ⟨(lt_of_lt_of_le hir (le_max' _ _ hr)).ne,
      (lt_of_le_of_lt (min'_le _ _ hl) hli).ne', hi⟩
  · rintro ⟨hMax, hMin, hi⟩
    exact ⟨hi, ⟨s.min' hs, min'_mem _ _, lt_of_le_of_ne (min'_le _ _ hi) hMin.symm⟩,
      ⟨s.max' hs, max'_mem _ _, lt_of_le_of_ne (le_max' _ _ hi) hMax⟩⟩

private lemma card_eq_middle_add_two {I : Type*} [LinearOrder I] {s : Finset I}
    (hs : 2 ≤ s.card) : s.card = (middle s).card + 2 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hlt : s.min' hne < s.max' hne := min'_lt_max'_of_card s (by omega)
  have hMax : s.max' hne ∈ s.erase (s.min' hne) :=
    mem_erase.mpr ⟨hlt.ne', max'_mem _ _⟩
  rw [middle_eq_erase hne, card_erase_of_mem hMax, card_erase_of_mem (min'_mem _ _)]
  omega

/-- Labels used by at least one block. -/
noncomputable def usedLabels {I V : Type*} [Fintype I] [Fintype V]
    (blocks : I → Finset V) : Finset V :=
  univ.filter fun v ↦ (occurrences blocks v).Nonempty

/-- The labels in block i that occur in a strictly earlier and strictly later block. -/
noncomputable def middleLabels {I V : Type*} [Fintype I] [LinearOrder I]
    (blocks : I → Finset V) (i : I) : Finset V :=
  (blocks i).filter fun v ↦ i ∈ middle (occurrences blocks v)

private lemma sum_card_incidence {I V : Type*} [Fintype I] [Fintype V]
    (A : I → Finset V) :
    (∑ i, (A i).card) = ∑ v, (occurrences A v).card := by
  have hA (i : I) : A i = univ.filter (· ∈ A i) := by
    rw [filter_mem_eq_inter, univ_inter]
  calc
    _ = ∑ i : I, ∑ v : V, if v ∈ A i then 1 else 0 :=
      sum_congr rfl fun i _ ↦ by
        conv_lhs => rw [hA i]
        rw [card_filter]
    _ = ∑ v : V, ∑ i : I, if v ∈ A i then 1 else 0 := Finset.sum_comm
    _ = _ := by simp only [occurrences, card_filter]

private lemma occurrences_middleLabels {I V : Type*} [Fintype I] [LinearOrder I]
    (blocks : I → Finset V) (v : V) :
    occurrences (middleLabels blocks) v = middle (occurrences blocks v) := by
  ext i
  change i ∈ univ.filter (fun j ↦ v ∈ middleLabels blocks j) ↔ _
  simp only [Finset.mem_filter, mem_univ, true_and]
  change v ∈ (blocks i).filter (fun w ↦ i ∈ middle (occurrences blocks w)) ↔ _
  rw [Finset.mem_filter]
  refine and_iff_right_of_imp fun hi ↦ ?_
  have hSub : middle (occurrences blocks v) ⊆ occurrences blocks v := filter_subset _ _
  have hOcc : i ∈ occurrences blocks v := hSub hi
  unfold occurrences at hOcc
  exact (mem_filter.mp hOcc).2

/-- The exact label accounting in the sharp graph-matrix trace estimate. -/
theorem sum_card_blocks {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (blocks : I → Finset V)
    (hRepeat : ∀ v, (occurrences blocks v).Nonempty → 2 ≤ (occurrences blocks v).card) :
    (∑ i, (blocks i).card) = 2 * (usedLabels blocks).card + ∑ i, (middleLabels blocks i).card := by
  have hOne (v : V) : (occurrences blocks v).card =
      (if (occurrences blocks v).Nonempty then 2 else 0) +
        (middle (occurrences blocks v)).card := by
    by_cases h : (occurrences blocks v).Nonempty
    · rw [ite_eq_left h, card_eq_middle_add_two (hRepeat v h), add_comm]
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp [middle]
  rw [sum_card_incidence blocks, sum_card_incidence (middleLabels blocks)]
  simp_rw [occurrences_middleLabels blocks, hOne, sum_add_distrib]
  congr 1
  rw [usedLabels, card_filter, mul_sum]
  exact sum_congr rfl fun v _ ↦ by split_ifs <;> simp

end LovaszTheta.Independent
