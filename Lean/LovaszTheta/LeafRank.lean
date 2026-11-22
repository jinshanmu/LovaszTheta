module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Rank and congruence counts for descendant-leaf rows

Disjoint nonempty supports give unit pivots over every cyclic group.
For a partition of the rows, a parent with a child across the cut
produces a nonzero vector in the intersection of the two spans.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- Prescribing sums on disjoint nonempty leaf sets removes one free residue for
each set, over every positive modulus. -/
theorem card_leaf_sum_fibre_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} [NeZero n] (R : κ → Finset ι) (hR : ∀ k, (R k).Nonempty)
    (hDisj : Pairwise fun k l ↦ Disjoint (R k) (R l)) (a : κ → ZMod n) :
    Fintype.card {x : ι → ZMod n // ∀ k, ∑ i ∈ R k, x i = a k} ≤
      n ^ (Fintype.card ι - Fintype.card κ) := by
  classical
  choose pivot hpivot using hR
  have hInj : Function.Injective pivot := by
    intro k l he
    by_contra hne
    exact Finset.disjoint_left.mp (hDisj hne) (hpivot k) (he ▸ hpivot l)
  let P := (univ : Finset κ).map ⟨pivot, hInj⟩
  let Fibre := {x : ι → ZMod n // ∀ k, ∑ i ∈ R k, x i = a k}
  let complement := {i : ι // i ∉ P}
  let restrict (x : Fibre) (i : complement) : ZMod n := x.val i.val
  have hRestrict : Function.Injective restrict := by
    intro x y hEq
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ P
    · obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hi
      change pivot k = i at hk
      subst i
      have hEqSum : (∑ j ∈ (R k).erase (pivot k), x.val j) =
          ∑ j ∈ (R k).erase (pivot k), y.val j := by
        apply sum_congr rfl
        intro j hj
        have hjP : j ∉ P := by
          intro hjP
          obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hjP
          change pivot l = j at hl
          have hlk : l ≠ k := by
            intro h
            subst l
            exact (mem_erase.mp hj).1 hl.symm
          exact Finset.disjoint_left.mp (hDisj hlk) (hpivot l) (hl ▸ (mem_erase.mp hj).2)
        exact congrFun hEq ⟨j, hjP⟩
      have hx := x.property k
      have hy := y.property k
      rw [← sum_erase_add _ _ (hpivot k)] at hx hy
      apply add_left_cancel (a := ∑ j ∈ (R k).erase (pivot k), x.val j)
      rw [hx, hEqSum, hy]
    · exact congrFun hEq ⟨i, hi⟩
  have hCard : Fintype.card complement = Fintype.card ι - Fintype.card κ := by
    change Fintype.card {i : ι // i ∉ P} = _
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_map, card_univ]
  calc
    Fintype.card Fibre ≤ Fintype.card (complement → ZMod n) :=
      Fintype.card_le_of_injective restrict hRestrict
    _ = _ := by rw [Fintype.card_fun, hCard, ZMod.card]

/-- The real rank of the rows indexed by a finite set of nodes. -/
noncomputable def leafRowRank {ι κ : Type*} (row : κ → ι → ℝ) (A : Finset κ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (row '' (↑A : Set κ)))

private lemma leafRowRank_add_of_crossing {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row : κ → ι → ℝ) (hSpan : Submodule.span ℝ (Set.range row) = ⊤)
    (A C : Finset κ) {p : κ} (hp : p ∈ A) (hC : (C \ A).Nonempty)
    (hRow : row p = ∑ t ∈ C, row t)
    (hnonneg : ∀ t, ∀ i, 0 ≤ row t i) (hpos : ∀ t, ∃ i, 0 < row t i) :
    Fintype.card ι + 1 ≤ leafRowRank row A + leafRowRank row Aᶜ := by
  classical
  let P := Submodule.span ℝ (row '' (↑A : Set κ))
  let Q := Submodule.span ℝ (row '' (↑Aᶜ : Set κ))
  let u := ∑ t ∈ C \ A, row t
  have hQ : u ∈ Q := by
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.subset_span ⟨t, Finset.mem_compl.mpr (Finset.mem_sdiff.mp ht).2, rfl⟩
  have hP : u ∈ P := by
    have hInside : (∑ t ∈ C ∩ A, row t) ∈ P := by
      apply Submodule.sum_mem
      intro t ht
      exact Submodule.subset_span ⟨t, (Finset.mem_inter.mp ht).2, rfl⟩
    have hSum : u + ∑ t ∈ C ∩ A, row t = row p := by
      rw [hRow]
      change (∑ t ∈ C \ A, row t) + ∑ t ∈ C ∩ A, row t = _
      rw [show C \ A = C \ (C ∩ A) by ext t; simp]
      exact Finset.sum_sdiff Finset.inter_subset_left
    have hEdit : u = row p - ∑ t ∈ C ∩ A, row t := eq_sub_iff_add_eq.mpr hSum
    rw [hEdit]
    exact P.sub_mem (Submodule.subset_span ⟨p, hp, rfl⟩) hInside
  have hu : u ≠ 0 := by
    obtain ⟨t, ht⟩ := hC
    obtain ⟨i, hi⟩ := hpos t
    have hUi : 0 < u i := by
      change 0 < (∑ s ∈ C \ A, row s) i
      rw [Finset.sum_apply]
      exact hi.trans_le (Finset.single_le_sum (fun s _ ↦ hnonneg s i) ht)
    intro h
    rw [h] at hUi
    exact lt_irrefl _ hUi
  have hSup : P ⊔ Q = ⊤ := by
    rw [← hSpan]
    apply le_antisymm
    · apply sup_le <;> apply Submodule.span_mono <;> exact Set.image_subset_range _ _
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      by_cases ht : t ∈ A
      · exact (le_sup_left : P ≤ P ⊔ Q) (Submodule.subset_span ⟨t, ht, rfl⟩)
      · exact (le_sup_right : Q ≤ P ⊔ Q)
          (Submodule.subset_span ⟨t, Finset.mem_compl.mpr ht, rfl⟩)
  have hInf : 0 < Module.finrank ℝ (P ⊓ Q : Submodule ℝ (ι → ℝ)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨u, hP, hQ⟩, fun h ↦ hu (congrArg Subtype.val h)⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hSup, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  change Fintype.card ι + 1 ≤ Module.finrank ℝ P + Module.finrank ℝ Q
  omega

/-- If the parent edges connect all nodes to a root and every parent row is
the sum of its child rows, every nontrivial cut increases the sum of the
two row ranks by at least one. -/
theorem leafRowRank_add_compl {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row : κ → ι → ℝ) (root : κ) (parent : κ → κ) (children : κ → Finset κ)
    (hRoot : ∀ t, ∃ h : ℕ, (parent^[h]) t = root)
    (hChild : ∀ t, t ∈ children (parent t) ∨ parent t = t)
    (hSum : ∀ t, (children t).Nonempty → row t = ∑ s ∈ children t, row s)
    (hSpan : Submodule.span ℝ (Set.range row) = ⊤)
    (hnonneg : ∀ t, ∀ i, 0 ≤ row t i) (hpos : ∀ t, ∃ i, 0 < row t i)
    (A : Finset κ) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    Fintype.card ι + 1 ≤ leafRowRank row A + leafRowRank row Aᶜ := by
  classical
  have hCut : ∃ t, ¬(t ∈ A ↔ parent t ∈ A) := by
    by_contra! h
    have hIter (t : κ) (k : ℕ) : t ∈ A ↔ (parent^[k]) t ∈ A := by
      induction k with
      | zero => rfl
      | succ k ih => exact ih.trans (by rw [Function.iterate_succ_apply']; exact h _)
    have hMem (t : κ) : t ∈ A ↔ root ∈ A := by
      obtain ⟨k, hk⟩ := hRoot t
      rw [← hk]
      exact hIter t k
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hAc
    exact Finset.mem_compl.mp hb ((hMem b).mpr ((hMem a).mp ha))
  obtain ⟨t, ht⟩ := hCut
  have hNe : parent t ≠ t := fun he ↦ ht (by rw [he])
  have hChildT := (hChild t).resolve_right hNe
  have hRow := hSum (parent t) ⟨t, hChildT⟩
  by_cases htA : t ∈ A
  · have hpA : parent t ∈ Aᶜ := Finset.mem_compl.mpr fun h ↦ ht (iff_of_true htA h)
    have hCN : (children (parent t) \ Aᶜ).Nonempty :=
      ⟨t, Finset.mem_sdiff.mpr ⟨hChildT, fun h ↦ Finset.mem_compl.mp h htA⟩⟩
    simpa only [compl_compl, add_comm] using
      leafRowRank_add_of_crossing row hSpan Aᶜ (children (parent t)) hpA hCN hRow hnonneg hpos
  · have hpA : parent t ∈ A := by
      by_contra h
      exact ht (iff_of_false htA h)
    exact leafRowRank_add_of_crossing row hSpan A (children (parent t)) hpA
      ⟨t, Finset.mem_sdiff.mpr ⟨hChildT, htA⟩⟩ hRow hnonneg hpos

end LovaszTheta.Circulant
