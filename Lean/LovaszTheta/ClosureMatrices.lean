module

public import LovaszTheta.WeightedChains
public import LovaszTheta.ClosureRecovery

/-!
# Adding the boundary edge to a matrix term

Adding the absent boundary edge multiplies an entry by its sign.
For separated pairs, the added edge connects the two boundaries
and lowers the remaining normalization power by one half.
-/

@[expose] public section

open Finset Matrix SimpleGraph Filter
open scoped Classical Matrix Matrix.Norms.L2Operator

namespace LovaszTheta.Independent

/-- Add the edge between the designated boundaries of a shape. -/
abbrev Shape.addBoundary (P : Shape) : Shape :=
  {P with graph := P.graph ⊔ edge P.left P.right}

/-- Multiplication by the signed adjacency at each entry. -/
noncomputable def closeEntries : MatrixFamily →ₗ[ℝ] MatrixFamily where
  toFun A := fun n x i j ↦ signedAdjacency x i j * A n x i j
  map_add' A B := by
    funext n x i j
    exact mul_add _ _ _
  map_smul' r A := by
    funext n x i j
    change signedAdjacency x i j * (r*A n x i j) = r*(signedAdjacency x i j*A n x i j)
    ring

private lemma labelledEdges_addBoundary {V : Type*} (P : Shape) (hNe : P.left ≠ P.right)
    (f : Fin P.vertexCount ↪ V) :
    labelledEdges P.addBoundary f =
      insert (edgeIndex (f P.left) (f P.right) (f.injective.ne hNe)) (labelledEdges P f) := by
  ext a
  rw [mem_insert,mem_labelledEdges_iff,mem_labelledEdges_iff]
  change a.val ∈ ((P.graph ⊔ edge P.left P.right).map f).edgeSet ↔ _
  rw [map_sup_embedding,edgeSet_sup]
  have he : ((edge P.left P.right).map f).edgeSet = {s(f P.left,f P.right)} := by
    rw [SimpleGraph.edgeSet_map,edgeSet_edge_of_ne hNe,Set.image_singleton]
    rfl
  rw [he,Set.mem_union,Set.mem_singleton_iff,or_comm]
  apply or_congr_left
  constructor
  · intro he
    exact Subtype.ext (show a.val = (edgeIndex (f P.left) (f P.right) (f.injective.ne hNe)).val from he)
  · exact fun he ↦ congrArg Subtype.val he

/-- The graph-matrix closure agrees with multiplication by the boundary sign. -/
theorem graphMatrix_addBoundary {V : Type*} [Fintype V] (P : Shape) (hNe : P.left ≠ P.right)
    (hG : ¬P.graph.Adj P.left P.right) (x : EdgeIndex V → Bool) (i j : V) :
    graphMatrix P.addBoundary x i j = signedAdjacency x i j * graphMatrix P x i j := by
  unfold graphMatrix
  rw [mul_sum]
  apply sum_congr rfl
  intro f _
  by_cases he : f P.left = i ∧ f P.right = j
  · have hn : i ≠ j := by rw [← he.1,← he.2]; exact f.injective.ne hNe
    have hEdge : edgeIndex (f P.left) (f P.right) (f.injective.ne hNe) = edgeIndex i j hn := by
      apply Subtype.ext
      change s(f P.left,f P.right) = s(i,j)
      rw [he.1,he.2]
    have hNo : edgeIndex (f P.left) (f P.right) (f.injective.ne hNe) ∉ labelledEdges P f := by
      intro h
      have he' := (mem_labelledEdges_iff P f _).mp h
      change (P.graph.map f).Adj (f P.left) (f P.right) at he'
      exact hG (SimpleGraph.map_adj_apply.mp he')
    change (if f P.left = i ∧ f P.right = j then walsh (labelledEdges P.addBoundary f) x else 0) = _
    rw [ite_eq_left he,ite_eq_left he,labelledEdges_addBoundary P hNe,walsh,prod_insert hNo,hEdge,
      signedAdjacency,dite_eq_left hn]
    rfl
  · change (if f P.left = i ∧ f P.right = j then walsh (labelledEdges P.addBoundary f) x else 0) = _
    rw [ite_eq_right he,ite_eq_right he,mul_zero]

lemma graphMatrix_diag_zero {V : Type*} [Fintype V] (P : Shape) (hNe : P.left ≠ P.right)
    (x : EdgeIndex V → Bool) (i : V) : graphMatrix P x i i = 0 := by
  unfold graphMatrix
  exact sum_eq_zero fun f _ ↦ ite_eq_right (fun h ↦ hNe (f.injective (h.1.trans h.2.symm)))

private lemma pair_span_pos (L R : Chain) : 0 < (ChainTerm.pair L R).span := by
  change 0 < Chain.span R + (Chain.span L+1)
  omega

private lemma pair_no_boundary_edge (L R : Chain) :
    ¬(ChainTerm.pair L R).graph.Adj (ChainTerm.pair L R).toShape.left (ChainTerm.pair L R).toShape.right := by
  intro he
  have hs := (ChainTerm.pair L R).no_cross_components he
  change (0 < Chain.span L+1) ↔ Chain.span R+(Chain.span L+1) < Chain.span L+1 at hs
  omega

private lemma mem_isolatedInterior_iff (Q : Shape) (i : Fin Q.vertexCount) :
    i ∈ Q.isolatedInterior ↔ i ≠ Q.left ∧ i ≠ Q.right ∧ ∀ j, ¬Q.graph.Adj i j := by
  unfold Shape.isolatedInterior
  simp only [mem_filter,mem_univ,true_and]

private lemma normVanishes_close_pair (L R : Chain) :
    NormVanishes (closeEntries (pairFamily (L,R))) := by
  let P := ChainTerm.pair L R
  have hNe : P.toShape.left ≠ P.toShape.right := fun he ↦ (Nat.ne_of_lt (pair_span_pos L R)) (congrArg Fin.val he)
  have hNo := pair_no_boundary_edge L R
  let Q := P.toShape.addBoundary
  have hIso : Q.isolatedInterior = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hI := (mem_isolatedInterior_iff Q i).mp hi
    obtain ⟨j,hj⟩ := P.incident_of_not_boundaries i hI.1 hI.2.1
    exact hI.2.2 j (Or.inl hj)
  have hAdj : Q.graph.Adj Q.left Q.right :=
    Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hNe⟩)
  have hInd : Q.boundaryIndicator = 1 := by
    unfold Shape.boundaryIndicator
    rw [ite_eq_left hAdj.reachable]
  have hPower : P.normalizationPower + roughExponent Q < 0 := by
    unfold roughExponent ChainTerm.normalizationPower
    rw [hIso,card_empty,hInd,show P.extra = 1 from rfl,Nat.cast_one]
    change -((P.span : ℝ)+1)/2 + (((P.span+1+0-1 : ℕ) : ℝ)/2) < 0
    simp only [Nat.add_zero,Nat.add_sub_cancel]
    linarith
  have hV := normVanishes_smul_graphMatrix Q (fun n ↦ (n : ℝ)^P.normalizationPower) zero_le_one hPower
    (Eventually.of_forall fun n ↦ by rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),one_mul])
  apply hV.congr
  apply Eventually.of_forall
  intro n x
  ext i j
  change (n : ℝ)^P.normalizationPower * graphMatrix Q x i j =
    signedAdjacency x i j * ((n : ℝ)^P.normalizationPower * graphMatrix P.toShape x i j)
  rw [graphMatrix_addBoundary _ hNe hNo]
  ring

/-- Closures of finite combinations of separated pairs have vanishing norm. -/
theorem normVanishes_close_pairSpace {A : MatrixFamily} (hA : A ∈ pairSpace) :
    NormVanishes (closeEntries A) := by
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨⟨L,R⟩,rfl⟩ := h
    exact normVanishes_close_pair L R
  | zero => rw [map_zero]; exact NormVanishes.of_zero
  | add A B _ _ hA hB => rw [map_add]; exact hA.add hB
  | smul r A _ hA => rw [map_smul]; exact hA.smul r

private lemma closure_isomorphic (C : Chain) (h : C ≠ []) :
    Nonempty ((C.close h).toShape.Isomorphism (ChainTerm.single C).toShape.addBoundary) := by
  let T := C.close h
  let P := ChainTerm.single C
  let e := finCongr (Chain.closure_size C h)
  let f := (Equiv.neg (Fin (T.additionalVertices+2))).trans e
  have hG : P.toShape.addBoundary.graph = C.closedGraph := by
    change P.graph ⊔ edge (0 : Fin (Chain.span C+1)) (Fin.last (Chain.span C)) = _
    rw [ChainTerm.graph_single]
    rfl
  refine ⟨⟨⟨f,?_⟩,?_,?_⟩⟩
  · intro a b
    change P.toShape.addBoundary.graph.Adj (e (-a)) (e (-b)) ↔ C.closedGraph.Adj (e (-a)) (e (-b))
    rw [hG]
  · exact Fin.ext (by change (-(0 : Fin (T.additionalVertices+2))).val = 0; simp)
  · apply Fin.ext
    change (-(1 : Fin (T.additionalVertices+2))).val = Chain.span C
    rw [← Fin.neg_last,neg_neg]
    have he := Chain.span_pos_of_ne_nil h
    change Chain.span C-1+1 = Chain.span C
    omega

/-- Closing a chain of at least two blocks gives the matrix of its constructed basic shape. -/
theorem closeEntries_chainFamily (C : Chain) (h : C ≠ []) (hj : 2 ≤ C.length) :
    closeEntries (chainFamily C) = blockFamily (C.close h) := by
  let P := ChainTerm.single C
  obtain ⟨e⟩ := closure_isomorphic C h
  have hNe : P.toShape.left ≠ P.toShape.right := fun he ↦
    (Nat.ne_of_lt (Chain.span_pos_of_ne_nil h)) (congrArg Fin.val he)
  have hNo : ¬P.toShape.graph.Adj P.toShape.left P.toShape.right := by
    intro hAdj
    have hG := ChainTerm.graph_single C
    change P.graph.Adj (0 : Fin (Chain.span C+1)) (Fin.last (Chain.span C)) at hAdj
    rw [hG] at hAdj
    exact Chain.no_boundary_edge_of_length_ge_two hj ((adjAt_iff_adj _ _ _).mpr hAdj)
  have hSize : (C.close h).span = Chain.span C := by
    have he := Chain.span_pos_of_ne_nil h
    change Chain.span C-1+1 = Chain.span C
    omega
  funext n x i j
  change signedAdjacency x i j * ((n : ℝ)^(-((Chain.span C : ℝ)+P.extra)/2) * graphMatrix P.toShape x i j) =
    (n : ℝ)^(-((C.close h).span : ℝ)/2) * graphMatrix (C.close h).toShape x i j
  rw [hSize,show P.extra = 0 from rfl,Nat.cast_zero,add_zero,e.graphMatrix_eq,graphMatrix_addBoundary _ hNe hNo]
  ring

lemma chainFamily_diag_of_ne_empty (C : Chain) (h : C ≠ []) (n : ℕ) (x : SignSample n) (i : Fin n) :
    chainFamily C n x i i = 0 := by
  have hn : (ChainTerm.single C).toShape.left ≠ (ChainTerm.single C).toShape.right :=
    fun he ↦ (Nat.ne_of_lt (Chain.span_pos_of_ne_nil h)) (congrArg Fin.val he)
  unfold chainFamily ChainTerm.matrix
  rw [Matrix.smul_apply,graphMatrix_diag_zero _ hn,smul_zero]

lemma pairSpace_diag_zero {A : MatrixFamily} (hA : A ∈ pairSpace)
    (n : ℕ) (x : SignSample n) (i : Fin n) : A n x i i = 0 := by
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨⟨L,R⟩,rfl⟩ := h
    have hNe : (ChainTerm.pair L R).toShape.left ≠ (ChainTerm.pair L R).toShape.right :=
      fun he ↦ (Nat.ne_of_lt (pair_span_pos L R)) (congrArg Fin.val he)
    unfold pairFamily ChainTerm.matrix
    rw [Matrix.smul_apply,graphMatrix_diag_zero _ hNe,smul_zero]
  | zero => rfl
  | add A B _ _ hA hB => exact (show A n x i i+B n x i i = 0 by rw [hA,hB,add_zero])
  | smul r A _ hA => exact (show r*A n x i i = 0 by rw [hA,mul_zero])

end LovaszTheta.Independent
