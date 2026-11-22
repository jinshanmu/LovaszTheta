module

public import LovaszTheta.ChainAlgebra
public import LovaszTheta.SharpNorm
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Empty chains, one block, and the single edge

The empty chain gives the identity. A single block is recognized
by the same path coordinates used in the append rule. The basic
shape of size two gives the signed adjacency matrix.
-/

@[expose] public section

open Finset SimpleGraph Matrix
open scoped Classical Matrix

namespace LovaszTheta.Independent

private lemma labelledEdges_empty {V : Type*} (P : Shape) (h : P.graph = ⊥)
    (f : Fin P.vertexCount ↪ V) : labelledEdges P f = ∅ := by
  ext a
  rw [mem_labelledEdges_iff,SimpleGraph.edgeSet_map,h]
  simp

/-- The normalized empty chain is the identity, at every order. -/
theorem chainFamily_nil : chainFamily [] = 1 := by
  funext n x i j
  let P := (ChainTerm.single []).toShape
  let : Unique (Fin P.vertexCount) := inferInstanceAs (Unique (Fin 1))
  have hG : P.graph = ⊥ := (ChainTerm.graph_single [])
  have hR : P.right = P.left := Subsingleton.elim _ _
  have hZ : ((ChainTerm.single []).span : ℝ) + (ChainTerm.single []).extra = 0 := by
    norm_num [ChainTerm.span,ChainTerm.offset,ChainTerm.extra]
  change (↑n : ℝ)^(-(((ChainTerm.single []).span : ℝ) + (ChainTerm.single []).extra)/2) *
    graphMatrix P x i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j
  rw [hZ,neg_zero,zero_div,Real.rpow_zero,one_mul,Matrix.one_apply]
  unfold graphMatrix
  simp only [hR,labelledEdges_empty P hG,walsh,prod_empty]
  let e : (Fin P.vertexCount ↪ Fin n) ≃ Fin n := Equiv.embeddingUnique
  have hEval (f : Fin P.vertexCount ↪ Fin n) : e f = f P.left :=
    congrArg f (Subsingleton.elim _ _)
  have he := Fintype.sum_equiv e
    (fun f ↦ if f P.left = i ∧ f P.left = j then (1 : ℝ) else 0)
    (fun a ↦ if a = i ∧ a = j then (1 : ℝ) else 0) (fun f ↦ by rw [hEval])
  rw [he]
  by_cases hj : i = j
  · subst j
    simp
  · rw [ite_eq_right hj]
    apply sum_eq_zero
    intro a _
    exact ite_eq_right (fun h ↦ hj (h.1.symm.trans h.2))

private lemma block_isomorphic_singleton (T : BasicShape) :
    Nonempty (T.toShape.Isomorphism (ChainTerm.single [T]).toShape) := by
  let P := ChainTerm.single []
  let e := P.appendedBlockEmb T
  have hCard : Fintype.card (Fin T.toShape.vertexCount) =
      Fintype.card (Fin (P.append T).toShape.vertexCount) := by
    simp only [Fintype.card_fin,ChainTerm.span_append]
    change T.span+1 = (0+T.span)+1
    omega
  let E := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective,hCard⟩)
  have hG : (P.append T).graph = T.graph.map e := by
    rw [P.graph_append T]
    have hMapBot : P.graph.map (P.prefixEmb T) = ⊥ := by
      let : Subsingleton (Fin (P.span+1)) := inferInstanceAs (Subsingleton (Fin 1))
      ext a b
      rw [SimpleGraph.map_adj (P.prefixEmb T)]
      refine iff_of_false ?_ (fun h ↦ h)
      rintro ⟨u,v,he,_,_⟩
      exact he.ne (Subsingleton.elim _ _)
    rw [hMapBot,bot_sup_eq]
    change T.pathGraph.map (P.tailEmb T) =
      T.graph.map ((P.tailEmb T) ∘ (Equiv.neg (Fin (T.span+1))).toEmbedding)
    rw [← SimpleGraph.map_map]
    congr 1
    exact SimpleGraph.comap_symm T.graph (Equiv.neg (Fin (T.span+1)))
  refine ⟨⟨⟨E,?_⟩,?_,?_⟩⟩
  · intro a b
    change (P.append T).graph.Adj (e a) (e b) ↔ T.graph.Adj a b
    rw [hG]
    exact SimpleGraph.map_adj_apply
  · exact (P.appendedBlockEmb_left T).trans (Fin.ext rfl)
  · exact P.appendedBlockEmb_right T

/-- A one-block chain has the normalized matrix of that basic block. -/
theorem chainFamily_singleton (T : BasicShape) : chainFamily [T] = blockFamily T := by
  funext n x
  have hV : (ChainTerm.single [T]).span = T.span := Nat.zero_add _
  have hE : (ChainTerm.single [T]).extra = 0 := rfl
  obtain ⟨e⟩ := block_isomorphic_singleton T
  unfold chainFamily blockFamily ChainTerm.matrix ChainTerm.blockMatrix
  rw [hV,hE,Nat.cast_zero,add_zero,e.graphMatrix_eq]

/-- The basic block consisting of a single edge. -/
def singleEdgeShape : BasicShape where
  additionalVertices := 0
  graph := cycleGraph 2
  cycle_le := le_rfl
  noncrossing := by
    intro a u b v ha hb hc
    have h₁ : a.val < u.val := ha
    have h₂ : u.val < b.val := hb
    have h₃ : b.val < v.val := hc
    have hv := v.isLt
    omega

@[simp]
lemma singleEdgeShape_reverse : singleEdgeShape.reverse = singleEdgeShape := by
  apply BasicShape.eq_of_graph_heq (T := singleEdgeShape.reverse) (U := singleEdgeShape) rfl
  apply heq_of_eq
  ext a b
  exact cycle_reverse_adj_iff a b

private lemma singleEdge_graph : singleEdgeShape.graph = edge 0 1 := by
  ext a b
  change Fin 2 at a b
  change (cycleGraph 2).Adj a b ↔ (edge (0 : Fin 2) 1).Adj a b
  rw [cycleGraph_two_eq_top,top_adj,edge_adj]
  refine ⟨fun h ↦ ⟨?_,h⟩,And.right⟩
  fin_cases a <;> fin_cases b
  · exact (h rfl).elim
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact (h rfl).elim

private lemma graphMatrix_singleEdge_apply_of_ne {V : Type*} [Fintype V]
    (x : EdgeIndex V → Bool) (i j : V) (hne : i ≠ j) :
    graphMatrix singleEdgeShape.toShape x i j = sign (x (edgeIndex i j hne)) := by
  let P := singleEdgeShape.toShape
  let f' : Fin 2 ↪ V := ⟨Fin.cases i (fun _ ↦ j),by
    intro a b he
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hne he).elim
    · exact (hne he.symm).elim
    · rfl⟩
  let f : Fin P.vertexCount ↪ V := f'
  have hi : f P.left = i := rfl
  have hj : f P.right = j := rfl
  have hUnique (g : Fin P.vertexCount ↪ V) : g P.left = i ∧ g P.right = j ↔ g = f := by
    constructor
    · rintro ⟨hI,hJ⟩
      ext p
      change Fin 2 at p
      fin_cases p
      · exact hI.trans hi.symm
      · exact hJ.trans hj.symm
    · rintro rfl
      exact ⟨hi,hj⟩
  have hEdges : labelledEdges P f = {edgeIndex i j hne} := by
    ext a
    rw [mem_labelledEdges_iff,SimpleGraph.edgeSet_map]
    have hG : P.graph = edge P.left P.right := singleEdge_graph
    rw [hG,edgeSet_edge_of_ne (show P.left ≠ P.right from (by decide : (0 : Fin 2) ≠ 1))]
    simp only [Set.image_singleton,Set.mem_singleton_iff,Function.Embedding.sym2Map_apply,
      Sym2.map_mk,hi,hj,mem_singleton]
    exact ⟨fun h ↦ Subtype.ext h,fun h ↦ congrArg Subtype.val h⟩
  change graphMatrix P x i j = _
  unfold graphMatrix
  simp only [hUnique,sum_ite_eq',mem_univ,ite_true,hEdges,walsh,prod_singleton]

/-- The single-edge graph matrix is exactly the signed adjacency matrix. -/
theorem graphMatrix_singleEdge {V : Type*} [Fintype V] (x : EdgeIndex V → Bool) :
    graphMatrix singleEdgeShape.toShape x = signedAdjacency x := by
  ext i j
  by_cases h : i = j
  · subst j
    rw [signedAdjacency_diag]
    unfold graphMatrix
    apply sum_eq_zero
    intro f _
    exact ite_eq_right (fun h ↦ (show singleEdgeShape.toShape.left ≠ singleEdgeShape.toShape.right from (by decide : (0 : Fin 2) ≠ 1))
      (f.injective (h.1.trans h.2.symm)))
  · rw [graphMatrix_singleEdge_apply_of_ne x i j h,signedAdjacency,dite_eq_left h]

/-- The normalized single edge gives the signed adjacency divided by `sqrt n`. -/
lemma blockFamily_singleEdge (n : ℕ) (x : SignSample n) :
    blockFamily singleEdgeShape n x = (1/Real.sqrt (n : ℝ)) • signedAdjacency x := by
  unfold blockFamily ChainTerm.blockMatrix
  rw [graphMatrix_singleEdge]
  congr 1
  rw [show singleEdgeShape.span = 1 from rfl,Nat.cast_one,neg_div,Real.rpow_neg (Nat.cast_nonneg _),Real.sqrt_eq_rpow]
  exact (one_div _).symm

end LovaszTheta.Independent
