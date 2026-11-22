module

public import LovaszTheta.SelectedLeafRows

/-!
# Descendant-leaf rank and residue fibers

The nonempty rows of the elimination form a basis of the selected
row span. Each has a unit pivot on a different leaf, giving the
modular count for prescribed node residues.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

private noncomputable def indicatorRow {I : Type*} [DecidableEq I] (s : Finset I) : I → ℝ :=
  fun i ↦ if i ∈ s then 1 else 0

private lemma indicatorRow_eq_sum {I : Type*} [DecidableEq I] (s : Finset I) :
    indicatorRow s = ∑ i ∈ s, (Pi.single i 1 : I → ℝ) := by
  funext i
  simp [indicatorRow, Pi.single_apply, apply_ite]

/-- The row with a one at each leaf below the given node. -/
noncomputable def leafRow (T : RootedTree) (v : T.Node) (i : T.Leaf) : ℝ :=
  if i ∈ T.descendantLeaves v then 1 else 0

lemma leafRow_eq_sum (T : RootedTree) (v : T.Node) :
    T.leafRow v = ∑ i ∈ T.descendantLeaves v, (Pi.single i 1 : T.Leaf → ℝ) :=
  indicatorRow_eq_sum (T.descendantLeaves v)

/-- The nonempty rows remaining after elimination. -/
noncomputable def nonemptyResidualRoles (T : RootedTree) (A : Finset T.Node) : Finset T.Node :=
  A.filter fun v ↦ (T.residualLeaves A v).Nonempty

private lemma residualRow_mem_span (T : RootedTree) (A : Finset T.Node)
    {v : T.Node} (hv : v ∈ A) :
    indicatorRow (T.residualLeaves A v) ∈ Submodule.span ℝ (T.leafRow '' (↑A : Set T.Node)) := by
  let P := Submodule.span ℝ (T.leafRow '' (↑A : Set T.Node))
  let x (i : T.Leaf) := P.mkQ (Pi.single i 1)
  have hZero (u : T.Node) (hu : u ∈ A) :
      (∑ i ∈ T.descendantLeaves u, x i) = ∑ _i ∈ T.descendantLeaves u, (0 : _ ⧸ P) := by
    dsimp only [x]
    rw [sum_const_zero, ← map_sum, ← T.leafRow_eq_sum u, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  have h := T.sum_residualLeaves_congr A x (fun _ ↦ 0) hZero v hv
  dsimp only [x] at h
  rwa [sum_const_zero, ← map_sum, ← indicatorRow_eq_sum, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h

private lemma independent_residualRows (T : RootedTree) (A : Finset T.Node) :
    LinearIndependent ℝ
      (fun v : T.nonemptyResidualRoles A ↦ indicatorRow (T.residualLeaves A v.val)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc v
  obtain ⟨i, hi⟩ := (mem_filter.mp v.property).2
  have hEval := congrFun hc i
  change (∑ u : T.nonemptyResidualRoles A, c u • indicatorRow (T.residualLeaves A u.val)) i = 0 at hEval
  rw [Fintype.sum_apply, Finset.sum_eq_single v] at hEval
  · simpa only [Pi.smul_apply, indicatorRow, hi, ite_true, smul_eq_mul, mul_one] using hEval
  · intro u _ hne
    have huv : u.val ≠ v.val := fun h ↦ hne (Subtype.ext h)
    have hu : i ∉ T.residualLeaves A u.val := fun h ↦
      Finset.disjoint_left.mp
        (T.residualLeaves_disjoint A (mem_filter.mp u.property).1 (mem_filter.mp v.property).1 huv) h hi
    simp [indicatorRow, hu]
  · intro hv
    exact (hv (mem_univ _)).elim

/-- The real rank is the number of disjoint nonempty rows after elimination. -/
theorem leafRowRank_eq_card_residual (T : RootedTree) (A : Finset T.Node) :
    leafRowRank T.leafRow A = (T.nonemptyResidualRoles A).card := by
  let P := Submodule.span ℝ (T.leafRow '' (↑A : Set T.Node))
  let r (v : T.nonemptyResidualRoles A) := indicatorRow (T.residualLeaves A v.val)
  let Q := Submodule.span ℝ (Set.range r)
  have hQP : Q ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact T.residualRow_mem_span A (mem_filter.mp v.property).1
  have hPQ : P ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change v ∈ A at hv
    rw [T.leafRow_eq_sum v, T.sum_descendantLeaves_eq_sum_residual hv]
    apply Submodule.sum_mem
    intro u hu
    rw [← indicatorRow_eq_sum]
    by_cases h : (T.residualLeaves A u).Nonempty
    · exact Submodule.subset_span ⟨⟨u, mem_filter.mpr ⟨(mem_filter.mp hu).1, h⟩⟩, rfl⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      have hZero : indicatorRow (∅ : Finset T.Leaf) = 0 := by ext i; simp [indicatorRow]
      rw [hZero]
      exact Q.zero_mem
  change Module.finrank ℝ P = _
  rw [le_antisymm hPQ hQP]
  exact (finrank_span_eq_card (T.independent_residualRows A)).trans (Fintype.card_coe _)

/-- Prescribing node residues on A leaves at most one free choice per
leaf outside the unit pivots, over every positive modulus. -/
theorem card_prescribed_residues_le (T : RootedTree) {n : ℕ} [NeZero n]
    (A : Finset T.Node) (a : T.Node → ZMod n) :
    Fintype.card {x : T.Leaf → ZMod n // ∀ v ∈ A, T.residue x v = a v} ≤
      n ^ (Fintype.card T.Leaf - leafRowRank T.leafRow A) := by
  let X := {x : T.Leaf → ZMod n // ∀ v ∈ A, T.residue x v = a v}
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    let U := ↥(T.nonemptyResidualRoles A)
    let R (u : U) := T.residualLeaves A u.val
    let b (u : U) := ∑ i ∈ R u, x₀.val i
    have hEq (x : X) (u : U) : (∑ i ∈ R u, x.val i) = b u := by
      apply T.sum_residualLeaves_congr A x.val x₀.val
      · intro v hv
        exact (x.property v hv).trans (x₀.property v hv).symm
      · exact (mem_filter.mp u.property).1
    let Y := {z : T.Leaf → ZMod n // ∀ u : U, ∑ i ∈ R u, z i = b u}
    let map (x : X) : Y := ⟨x.val, hEq x⟩
    have hInj : Function.Injective map := fun _ _ he ↦ Subtype.ext
      (congrArg (fun z : Y ↦ z.val) he)
    refine (Fintype.card_le_of_injective map hInj).trans ?_
    have h := card_leaf_sum_fibre_le R (fun u ↦ (mem_filter.mp u.property).2)
      (fun u v hne ↦ T.residualLeaves_disjoint A (mem_filter.mp u.property).1
        (mem_filter.mp v.property).1 (fun h ↦ hne (Subtype.ext h))) b
    rw [Fintype.card_coe, ← leafRowRank_eq_card_residual] at h
    have hCard (f₁ f₂ : Fintype Y) : @Fintype.card Y f₁ = @Fintype.card Y f₂ :=
      congrArg (fun f ↦ @Fintype.card Y f) (Subsingleton.elim _ _)
    exact (hCard _ _).trans_le h
  · have : IsEmpty X := not_nonempty_iff.mp hX
    change Fintype.card X ≤ _
    rw [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

end LovaszTheta.Circulant.RootedTree
