module

public import LovaszTheta.IdentificationProduct
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Removing isolated interior vertices

Once the labels of the retained shape are chosen, the isolated
vertices are injected into the unused labels. Their number of
extensions is a falling factorial, independent of the retained labels.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Independent

variable {K A : Shape}

/-- Separate the retained vertices from their complement. -/
noncomputable def retainedSumEquiv (e : Fin K.vertexCount ↪ Fin A.vertexCount) :
    Fin K.vertexCount ⊕ ((Set.range e)ᶜ : Set (Fin A.vertexCount)) ≃ Fin A.vertexCount :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)

/-- Split a full labeling into a retained labeling and an injection into the unused labels. -/
noncomputable def extensionEquiv {V : Type*} (e : Fin K.vertexCount ↪ Fin A.vertexCount) :
    (Fin A.vertexCount ↪ V) ≃
      (Σ f : Fin K.vertexCount ↪ V, ((Set.range e)ᶜ : Set (Fin A.vertexCount)) ↪
        ((Set.range f)ᶜ : Set V)) :=
  (Equiv.embeddingCongr (retainedSumEquiv e).symm (Equiv.refl V)).trans
    Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

private lemma extensionEquiv_fst {V : Type*} (e : Fin K.vertexCount ↪ Fin A.vertexCount)
    (f : Fin A.vertexCount ↪ V) : (extensionEquiv e f).1 = e.trans f := rfl

private lemma labelledEdges_eq_restrict {V : Type*} (e : Fin K.vertexCount ↪ Fin A.vertexCount)
    (hG : A.graph = K.graph.map e) (f : Fin A.vertexCount ↪ V) :
    labelledEdges A f = labelledEdges K (e.trans f) := by
  ext a
  rw [mem_labelledEdges_iff,mem_labelledEdges_iff,hG,SimpleGraph.map_map]
  rfl

/-- The extension factor for a shape obtained by adding isolated vertices
away from the boundaries. -/
theorem graphMatrix_eq_descFactorial_smul {V : Type*} [Fintype V] (e : Fin K.vertexCount ↪ Fin A.vertexCount)
    (hG : A.graph = K.graph.map e) (hLeft : e K.left = A.left) (hRight : e K.right = A.right)
    (x : EdgeIndex V → Bool) :
    graphMatrix A x = (((Fintype.card V - K.vertexCount).descFactorial (A.vertexCount-K.vertexCount) : ℕ) : ℝ)
      • graphMatrix K x := by
  ext i j
  have hTerm (f : Fin A.vertexCount ↪ V) :
      (if f A.left = i ∧ f A.right = j then walsh (labelledEdges A f) x else 0) =
      if (extensionEquiv e f).1 K.left = i ∧ (extensionEquiv e f).1 K.right = j then
        walsh (labelledEdges K (extensionEquiv e f).1) x else 0 := by
    rw [extensionEquiv_fst,labelledEdges_eq_restrict e hG,Function.Embedding.trans_apply,
      Function.Embedding.trans_apply,hLeft,hRight]
  simp only [graphMatrix,Matrix.smul_apply,smul_eq_mul]
  let term (f : Fin K.vertexCount ↪ V) :=
    if f K.left = i ∧ f K.right = j then walsh (labelledEdges K f) x else 0
  rw [Fintype.sum_equiv (extensionEquiv e) _ (fun fg ↦ term fg.1) hTerm]
  rw [Fintype.sum_sigma' (fun (f : Fin K.vertexCount ↪ V) (_ : ((Set.range e)ᶜ : Set (Fin A.vertexCount)) ↪ ((Set.range f)ᶜ : Set V)) ↦ term f)]
  simp only [sum_const,card_univ,Fintype.card_embedding_eq,Fintype.card_compl_set,Fintype.card_range,
    Fintype.card_fin,nsmul_eq_mul,mul_sum]
  rfl

end LovaszTheta.Independent
