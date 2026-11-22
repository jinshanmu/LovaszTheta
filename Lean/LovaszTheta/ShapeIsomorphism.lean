module

public import LovaszTheta.GraphMatrices

/-!
# Invariance under relabeling a shape

A boundary-preserving isomorphism transports injective
labelings and their edge sign sets bijectively.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

/-- An isomorphism preserving the ordered boundaries of two shapes. -/
structure Shape.Isomorphism (S T : Shape) where
  /-- The isomorphism of their underlying graphs. -/
  graphIso : S.graph ≃g T.graph
  map_left : graphIso S.left = T.left
  map_right : graphIso S.right = T.right

namespace Shape.Isomorphism

variable {S T : Shape}

/-- The isomorphism on the unordered edge types. -/
def edgeEquiv (e : S.Isomorphism T) : S.graph.edgeSet ≃ T.graph.edgeSet where
  toFun a := ⟨a.val.map e.graphIso,e.graphIso.map_mem_edgeSet_iff.mpr a.property⟩
  invFun a := ⟨a.val.map e.graphIso.symm,e.graphIso.symm.map_mem_edgeSet_iff.mpr a.property⟩
  left_inv a := Subtype.ext (by
    change (a.val.map e.graphIso).map e.graphIso.symm = a.val
    rw [Sym2.map_map]
    exact (congrArg (fun f ↦ a.val.map f) (funext fun v ↦ e.graphIso.toEquiv.symm_apply_apply v)).trans
      (congrFun Sym2.map_id' a.val))
  right_inv a := Subtype.ext (by
    change (a.val.map e.graphIso.symm).map e.graphIso = a.val
    rw [Sym2.map_map]
    exact (congrArg (fun f ↦ a.val.map f) (funext fun v ↦ e.graphIso.toEquiv.apply_symm_apply v)).trans
      (congrFun Sym2.map_id' a.val))

/-- Transport each labeling of the target shape to a labeling of the source. -/
def labelingEquiv (e : S.Isomorphism T) (V : Type*) :
    (Fin T.vertexCount ↪ V) ≃ (Fin S.vertexCount ↪ V) :=
  Equiv.embeddingCongr e.graphIso.toEquiv.symm (Equiv.refl V)

lemma labelingEquiv_apply {V : Type*} (e : S.Isomorphism T) (f : Fin T.vertexCount ↪ V)
    (u : Fin S.vertexCount) : labelingEquiv e V f u = f (e.graphIso u) := rfl

lemma labelledEdges_eq {V : Type*} (e : S.Isomorphism T) (f : Fin T.vertexCount ↪ V) :
    labelledEdges S (labelingEquiv e V f) = labelledEdges T f := by
  unfold labelledEdges
  have he : edgeEmbedding S (labelingEquiv e V f) = e.edgeEquiv.toEmbedding.trans (edgeEmbedding T f) := by
    apply Function.Embedding.ext
    intro a
    apply Subtype.ext
    change a.val.map (labelingEquiv e V f) = (a.val.map e.graphIso).map f
    rw [Sym2.map_map]
    rfl
  rw [he,← map_map,map_univ_equiv]

lemma graphMatrix_eq {V : Type*} [Fintype V] (e : S.Isomorphism T) (x : EdgeIndex V → Bool) :
    graphMatrix S x = graphMatrix T x := by
  ext i j
  unfold graphMatrix
  symm
  refine Fintype.sum_equiv (labelingEquiv e V) _ _ fun f ↦ ?_
  simp only [labelingEquiv_apply,e.map_left,e.map_right,e.labelledEdges_eq]

end Shape.Isomorphism

end LovaszTheta.Independent
