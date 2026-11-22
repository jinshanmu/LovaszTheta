module

public import LovaszTheta.VertexIdentifications

/-!
# The graph-matrix product over identifications

Within each identification, the common signs square to one.
The surviving signs are precisely the edges of the quotient graph.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix symmDiff

namespace LovaszTheta.Independent

variable {V : Type*}

lemma mem_labelledEdges_iff (P : Shape) (f : Fin P.vertexCount ↪ V) (a : EdgeIndex V) :
    a ∈ labelledEdges P f ↔ a.val ∈ (P.graph.map f).edgeSet := by
  rw [labelledEdges,mem_map,SimpleGraph.edgeSet_map]
  simp only [Set.mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨e,h⟩
    exact ⟨e.val,e.property,congrArg Subtype.val h⟩
  · rintro ⟨e,h,he⟩
    exact ⟨⟨e,h⟩,Subtype.ext he⟩

namespace Identification

variable {P S : Shape} (p : Identification P S) [Fintype V]

private lemma sum_join {U : Type*} [Fintype U] (a b : U) {R : Type*} [AddCommMonoid R] (r : R) :
    (∑ u : U, if a = u ∧ b = u then r else 0) = if a = b then r else 0 := by
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    exact sum_eq_zero (fun u _ ↦ ite_eq_right (fun hu ↦ h (hu.1.trans hu.2.symm)))

private lemma graphMatrix_mul_sum_compatible (P S : Shape) (x : EdgeIndex V → Bool) (i k : V) :
    (graphMatrix P x * graphMatrix S x) i k =
      ∑ fg : Compatible P S V,
        if fg.val.1 P.left = i ∧ fg.val.2 S.right = k then
          walsh (labelledEdges P fg.val.1 ∆ labelledEdges S fg.val.2) x else 0 := by
  rw [graphMatrix_mul_apply,sum_comm]
  simp_rw [sum_comm (s := (univ : Finset V))]
  have hTerm (f : Fin P.vertexCount ↪ V) (g : Fin S.vertexCount ↪ V) :
      (∑ j, if (f P.left = i ∧ f P.right = j) ∧ (g S.left = j ∧ g S.right = k)
        then walsh (labelledEdges P f ∆ labelledEdges S g) x else 0) =
      if f P.right = g S.left then if f P.left = i ∧ g S.right = k
        then walsh (labelledEdges P f ∆ labelledEdges S g) x else 0 else 0 := by
    by_cases h : f P.left = i ∧ g S.right = k
    · simp only [h.1,h.2,true_and,and_true,ite_true]
      exact sum_join _ _ _
    · rw [ite_eq_right h,ite_self]
      exact sum_eq_zero (fun j _ ↦ ite_eq_right (fun hj ↦ h ⟨hj.1.1,hj.2.2⟩))
  simp_rw [hTerm]
  rw [← Fintype.sum_prod_type']
  rw [← sum_filter]
  exact sum_subtype _ (fun z ↦ by simp) _

omit [Fintype V] in
private lemma edgeSet_remaining_map (f : p.Vertex ↪ V) :
    (p.remaining.map f).edgeSet =
      (P.graph.map (p.old.trans f)).edgeSet ∆ (S.graph.map (p.new.trans f)).edgeSet := by
  have hA : (p.oldGraph.map f).edgeSet = (P.graph.map (p.old.trans f)).edgeSet := by
    simp only [oldGraph,SimpleGraph.map_map]
    rfl
  have hB : (p.newGraph.map f).edgeSet = (S.graph.map (p.new.trans f)).edgeSet := by
    simp only [newGraph,SimpleGraph.map_map]
    rfl
  rw [← hA,← hB]
  simp only [remaining,SimpleGraph.edgeSet_map,SimpleGraph.edgeSet_sup,SimpleGraph.edgeSet_sdiff]
  exact Set.image_symmDiff (Sym2.map.injective f.injective) _ _

/-- The numbering of the quotient vertices in the resulting shape. -/
noncomputable def numbering : p.Vertex ≃ Fin p.shape.vertexCount := Fintype.equivFin p.Vertex

omit [Fintype V] in
private lemma labelledEdges_shape_eq (f : p.Vertex ↪ V) :
    labelledEdges p.shape (p.numbering.symm.toEmbedding.trans f) =
      labelledEdges P (p.old.trans f) ∆ labelledEdges S (p.new.trans f) := by
  let e := p.numbering
  have hGraph : (p.shape.graph.map (e.symm.toEmbedding.trans f)) = p.remaining.map f := by
    have hC : p.shape.graph = p.remaining.map e.toEmbedding := SimpleGraph.comap_symm _ _
    rw [hC,SimpleGraph.map_map]
    congr 1
    funext u
    change f (e.symm (e u)) = f u
    rw [e.symm_apply_apply]
  ext a
  rw [mem_labelledEdges_iff,hGraph,edgeSet_remaining_map,Set.mem_symmDiff,Finset.mem_symmDiff,
    mem_labelledEdges_iff,mem_labelledEdges_iff]

private lemma graphMatrix_shape_eq_sum (x : EdgeIndex V → Bool) (i k : V) :
    graphMatrix p.shape x i k = ∑ f : p.Vertex ↪ V,
      if f (p.old P.left) = i ∧ f (p.new S.right) = k then
        walsh (labelledEdges P (p.old.trans f) ∆ labelledEdges S (p.new.trans f)) x else 0 := by
  let e := p.numbering
  symm
  unfold graphMatrix
  apply Fintype.sum_equiv (Equiv.embeddingCongr e (Equiv.refl V))
  intro f
  change (if f (p.old P.left) = i ∧ f (p.new S.right) = k then _ else _) =
    (if f (e.symm (e (p.old P.left))) = i ∧ f (e.symm (e (p.new S.right))) = k then
      walsh (labelledEdges p.shape (e.symm.toEmbedding.trans f)) x else 0)
  rw [e.symm_apply_apply,e.symm_apply_apply,labelledEdges_shape_eq]

/-- The exact expansion of a product as a sum over partial identifications. -/
theorem graphMatrix_mul_eq_sum (P S : Shape) (x : EdgeIndex V → Bool) :
    graphMatrix P x * graphMatrix S x = ∑ p : Identification P S, graphMatrix p.shape x := by
  ext i k
  rw [graphMatrix_mul_sum_compatible]
  simp only [Matrix.sum_apply,graphMatrix_shape_eq_sum]
  rw [← Fintype.sum_sigma']
  symm
  apply Fintype.sum_equiv (labelingEquiv P S V).symm
  rintro ⟨p,f⟩
  rfl

end Identification

end LovaszTheta.Independent
