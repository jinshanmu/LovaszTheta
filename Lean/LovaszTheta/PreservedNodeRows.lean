module

public import LovaszTheta.SignedNodeMatches

/-!
# Signed matches that preserve the parent relations

Parent sums determine every node value from the leaf values. A
preserving signed permutation therefore determines a matching
assignment over every modulus and sends the real row spans to one
another when the leaf counts agree.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

namespace RootedTree

/-- Values on the leaves uniquely extend to node values satisfying the
parent-sum rule. -/
lemma nodeValues_eq_sum_leaves {G : Type*} [AddCommMonoid G] (T : RootedTree)
    (y : T.Node → G) (h : ∀ v, (T.children v).Nonempty → y v = ∑ w ∈ T.children v, y w)
    (u : T.Node) :
    y u = ∑ i ∈ T.descendantLeaves u, y i.val := by
  let maxDepth := (univ : Finset T.Node).sup T.depth
  have hMax (v : T.Node) : T.depth v ≤ maxDepth := le_sup (mem_univ v)
  induction hm : maxDepth - T.depth u using Nat.strong_induction_on generalizing u with
  | ind m ih =>
    by_cases hCh : (T.children u).Nonempty
    · calc
        y u = ∑ w ∈ T.children u, y w := h u hCh
        _ = ∑ w ∈ T.children u, ∑ i ∈ T.descendantLeaves w, y i.val := by
          apply sum_congr rfl
          intro w hw
          obtain ⟨hne, hPar⟩ := (T.mem_children_iff u w).mp hw
          have hRoot : w ≠ T.root := fun he ↦ hne (by simpa only [he, T.parent_root] using hPar)
          have hDepth := T.depth_parent_lt w hRoot
          rw [hPar] at hDepth
          exact ih _ (by have := hMax w; omega) w rfl
        _ = _ := by
          rw [T.descendantLeaves_eq_children hCh, sum_biUnion]
          exact fun _ hw _ hv hne ↦ children_descendantLeaves_disjoint hw hv hne
    · let v : T.Leaf := ⟨u, fun w hw ↦ by
        by_contra hne
        exact hCh ⟨w, (T.mem_children_iff u w).mpr ⟨hne, hw⟩⟩⟩
      have he : T.descendantLeaves u = {v} := T.descendantLeaves_leaf v
      rw [he, sum_singleton]

end RootedTree

namespace SignedNodeMatch

variable {T S : RootedTree}

/-- A preserving match fixes the target assignment from the source
leaves, with all node relations valid modulo n. -/
theorem matches_of_preserves {n : ℕ} (M : SignedNodeMatch T S)
    (h : M.PreservesParentSums) (a : T.Leaf → ZMod n) :
    M.Matches a (fun i ↦ M.value a i.val) := by
  have hp (v : S.Node) (hv : (S.children v).Nonempty) :
      M.value a v = ∑ w ∈ S.children v, M.value a w := by
    have hp := M.sum_parentRelation_mul v a
    simp only [h v hv, Int.cast_zero, zero_mul, sum_const_zero] at hp
    exact sub_eq_zero.mp hp.symm
  intro v
  exact (S.nodeValues_eq_sum_leaves (M.value a) hp v).symm

/-- The signed integer row regarded as a real vector on the source leaves. -/
noncomputable def realRow (M : SignedNodeMatch T S) (v : S.Node) (i : T.Leaf) : ℝ :=
  M.row v i

lemma realRow_eq (M : SignedNodeMatch T S) (v : S.Node) :
    M.realRow v = if M.orient v then T.leafRow (M.node v) else -T.leafRow (M.node v) := by
  funext i
  cases h : M.orient v <;> simp [realRow, row, h, RootedTree.leafRow, RootedTree.leafRowInt]

/-- Pull a target leaf row back through the signed source rows of the
target leaves. -/
noncomputable def rowMap (M : SignedNodeMatch T S) : (S.Leaf → ℝ) →ₗ[ℝ] (T.Leaf → ℝ) where
  toFun x := ∑ j, x j • M.realRow j.val
  map_add' := by intro x y; simp only [Pi.add_apply, add_smul, sum_add_distrib]
  map_smul' := by
    intro a x
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply]

lemma realRow_eq_sum_leaves (M : SignedNodeMatch T S) (h : M.PreservesParentSums) (v : S.Node) :
    M.realRow v = ∑ j ∈ S.descendantLeaves v, M.realRow j.val := by
  have hPar (u : S.Node) (hu : (S.children u).Nonempty) :
      M.realRow u = ∑ w ∈ S.children u, M.realRow w := by
    funext i
    rw [Finset.sum_apply]
    change (M.row u i : ℝ) = ∑ w ∈ S.children u, (M.row w i : ℝ)
    rw [← Int.cast_sum]
    exact_mod_cast sub_eq_zero.mp (h u hu i)
  exact S.nodeValues_eq_sum_leaves M.realRow hPar v

lemma rowMap_leafRow (M : SignedNodeMatch T S) (h : M.PreservesParentSums) (v : S.Node) :
    M.rowMap (S.leafRow v) = M.realRow v := by
  change (∑ j, S.leafRow v j • M.realRow j.val) = M.realRow v
  simp only [RootedTree.leafRow]
  simp_rw [ite_smul, one_smul, zero_smul]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  exact (M.realRow_eq_sum_leaves h v).symm

private lemma rowMap_surjective (M : SignedNodeMatch T S) (h : M.PreservesParentSums) :
    Function.Surjective M.rowMap := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← T.span_leafRows]
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  let v := M.node.symm u
  have hRow := M.rowMap_leafRow h v
  rw [M.realRow_eq, show M.node v = u from M.node.apply_symm_apply u] at hRow
  by_cases he : M.orient v
  · exact ⟨S.leafRow v, by simpa [he] using hRow⟩
  · refine ⟨-S.leafRow v, ?_⟩
    rw [map_neg, hRow, ite_eq_right he, neg_neg]

/-- Preserving signed matches between equal leaf dimensions take the
rank of every selected set of rows to the rank of its matched set. -/
theorem leafRowRank_map_eq (M : SignedNodeMatch T S) (h : M.PreservesParentSums)
    (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) (A : Finset S.Node) :
    leafRowRank S.leafRow A = leafRowRank T.leafRow (A.map M.node.toEmbedding) := by
  have hDim : Module.finrank ℝ (S.Leaf → ℝ) = Module.finrank ℝ (T.Leaf → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hL
  have hS := M.rowMap_surjective h
  have hI := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hDim).mpr hS
  let e := LinearEquiv.ofBijective M.rowMap ⟨hI, hS⟩
  let P := Submodule.span ℝ (S.leafRow '' (↑A : Set S.Node))
  let Q := Submodule.span ℝ (T.leafRow '' (↑(A.map M.node.toEmbedding) : Set T.Node))
  have hQ : P.map M.rowMap = Q := by
    unfold P Q
    rw [Submodule.map_span]
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      rw [M.rowMap_leafRow h v, M.realRow_eq]
      have hV := Submodule.subset_span (R := ℝ)
        (s := T.leafRow '' (↑(A.map M.node.toEmbedding) : Set T.Node))
        ⟨M.node v, mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
      split_ifs
      · exact hV
      · exact Submodule.neg_mem _ hV
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hu
      have hI := Submodule.subset_span (R := ℝ)
        (s := M.rowMap '' (S.leafRow '' (↑A : Set S.Node))) ⟨S.leafRow v, ⟨v, hv, rfl⟩, rfl⟩
      rw [M.rowMap_leafRow h v, M.realRow_eq] at hI
      split_ifs at hI
      · exact hI
      · exact (Submodule.neg_mem_iff _).mp hI
  change Module.finrank ℝ P = Module.finrank ℝ Q
  rw [← hQ]
  exact (e.finrank_map_eq P).symm

end SignedNodeMatch

end LovaszTheta.Circulant
