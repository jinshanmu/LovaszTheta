module

public import LovaszTheta.TraceDefect

/-!
# Counting the unpaired trace blocks

An edge can occur in at most one forward block and at most one
return block. Thus each exceptional position has only a bounded
number of simple neighbors through one or two shared edges.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l : ℕ} (c : TraceBlocks V (l+2))

/-- Positions belonging to no exact pair. -/
noncomputable def unpairedPositions : Finset (Fin (l+2)) :=
  univ.filter fun i ↦ ¬∃ j, exactPair c.block i j ∨ exactPair c.block j i

/-- Simple positions sharing at least one labeled edge with the indicated block. -/
noncomputable def simpleNeighbors (i : Fin (l+2)) : Finset (Fin (l+2)) :=
  univ.filter fun j ↦ simplePosition c.block j ∧ ShareEdge c.block i j

lemma mem_unpairedPositions {i : Fin (l+2)} :
    i ∈ c.unpairedPositions ↔ ¬∃ j, exactPair c.block i j ∨ exactPair c.block j i := by
  unfold unpairedPositions
  rw [Finset.mem_filter]
  simp only [mem_univ,true_and]

lemma mem_simpleNeighbors {i j : Fin (l+2)} :
    j ∈ c.simpleNeighbors i ↔ simplePosition c.block j ∧ ShareEdge c.block i j := by
  unfold simpleNeighbors
  rw [Finset.mem_filter]
  simp only [mem_univ,true_and]

private lemma unique_first_of_common_edge {i j : Fin (l+2)} (hI : firstEdges c.block i)
    (hJ : firstEdges c.block j) (he : ShareEdge c.block i j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hJ i hij he.symm
  · exact hI j hji he

private lemma unique_last_of_common_edge {i j : Fin (l+2)} (hI : lastEdges c.block i)
    (hJ : lastEdges c.block j) (he : ShareEdge c.block i j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hI j hij he
  · exact hJ i hji he.symm

/-- For any labeled edge of a block there are at most two simple
neighbors using that edge, one first and one last. -/
theorem card_simpleNeighbors_le (h : c.RepeatedEdges) (i : Fin (l+2)) :
    (c.simpleNeighbors i).card ≤ 2*((c.block i).shape.additionalVertices+2)^2 := by
  let N := (c.block i).shape.additionalVertices+2
  let S := c.simpleNeighbors i
  have exists_edge (j : S) : ∃ a b : Fin N, (c.block j.val).graph.Adj ((c.block i).label a) ((c.block i).label b) := by
    obtain ⟨u,v,hi,hj⟩ := (c.mem_simpleNeighbors.mp j.property).2
    obtain ⟨a,b,_,rfl,rfl⟩ :=
      (SimpleGraph.map_adj (c.block i).label (c.block i).shape.graph u v).mp hi
    exact ⟨a,b,hj⟩
  choose a b hb using exists_edge
  let tag (j : S) : Bool := if firstEdges c.block j.val then true else false
  let code (j : S) : (Fin N × Fin N) × Bool := ((a j,b j),tag j)
  have hCode : Function.Injective code := by
    intro j k he
    have ha : a j = a k := congrArg (fun p : (Fin N × Fin N) × Bool ↦ p.1.1) he
    have hb' : b j = b k := congrArg (fun p : (Fin N × Fin N) × Bool ↦ p.1.2) he
    have hTag : tag j = tag k := congrArg Prod.snd he
    have hShare : ShareEdge c.block j.val k.val := by
      refine ⟨(c.block i).label (a j),(c.block i).label (b j),hb j,?_⟩
      rw [ha,hb']
      exact hb k
    apply Subtype.ext
    by_cases hj : firstEdges c.block j.val
    · have hk : firstEdges c.block k.val := by
        by_contra hn
        simp only [tag,ite_eq_left hj,ite_eq_right hn,Bool.true_eq_false] at hTag
      exact c.unique_first_of_common_edge hj hk hShare
    · have hk : ¬firstEdges c.block k.val := by
        intro hK
        simp only [tag,ite_eq_right hj,ite_eq_left hK,Bool.false_eq_true] at hTag
      exact c.unique_last_of_common_edge
        ((firstEdges_or_lastEdges h j.val (c.mem_simpleNeighbors.mp j.property).1).resolve_left hj)
        ((firstEdges_or_lastEdges h k.val (c.mem_simpleNeighbors.mp k.property).1).resolve_left hk) hShare
  have hCard := Fintype.card_le_of_injective code hCode
  simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hCard
  exact hCard.trans_eq (by dsimp only [N]; ring)

/-- The unpaired blocks are few compared with the defect. -/
theorem card_unpairedPositions_le (h : c.RepeatedEdges) {v : ℕ}
    (hSize : ∀ i, (c.block i).shape.additionalVertices+2 ≤ v) :
    c.unpairedPositions.card ≤ (1+2*v^2+(2*v^2)^2)*c.defect := by
  let E := c.exceptionalPositions
  let S := E.biUnion c.simpleNeighbors
  let T := S.biUnion c.simpleNeighbors
  let B := 2*v^2
  have hSub : c.unpairedPositions ⊆ E ∪ S ∪ T := by
    intro i hi
    by_cases hI : i ∈ E
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hI)))
    have hSimple : simplePosition c.block i := by
      by_contra hn
      exact hI (mem_filter.mpr ⟨mem_univ _,hn⟩)
    rcases nearExceptional_of_unpaired h hSimple (c.mem_unpairedPositions.mp hi) with
      ⟨j,hj,hE⟩ | ⟨j,k,hj,hSimpleJ,hk,hE⟩
    · have hMem : i ∈ S := mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hE⟩,
        c.mem_simpleNeighbors.mpr ⟨hSimple,hj.symm⟩⟩
      exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hMem)))
    · have hMem : j ∈ S := mem_biUnion.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,hE⟩,
        c.mem_simpleNeighbors.mpr ⟨hSimpleJ,hk.symm⟩⟩
      exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j,hMem,c.mem_simpleNeighbors.mpr ⟨hSimple,hj.symm⟩⟩))
  have hEach (i : Fin (l+2)) : (c.simpleNeighbors i).card ≤ B :=
    (c.card_simpleNeighbors_le h i).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hSize i) _))
  have hNeighbors (U : Finset (Fin (l+2))) : (U.biUnion c.simpleNeighbors).card ≤ B*U.card :=
    card_biUnion_le.trans ((sum_le_sum fun i _ ↦ hEach i).trans_eq
      (by rw [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]))
  have hE : E.card ≤ c.defect := c.card_exceptionalPositions_le
  have hS : S.card ≤ B*c.defect := (hNeighbors E).trans (Nat.mul_le_mul_left _ hE)
  have hT : T.card ≤ B*(B*c.defect) := (hNeighbors S).trans (Nat.mul_le_mul_left _ hS)
  calc
    _ ≤ (E ∪ S ∪ T).card := card_le_card hSub
    _ ≤ E.card+S.card+T.card := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ c.defect+B*c.defect+B*(B*c.defect) := Nat.add_le_add (Nat.add_le_add hE hS) hT
    _ = _ := by unfold B; ring

end LovaszTheta.Independent.TraceBlocks
