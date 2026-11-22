module

public import LovaszTheta.RoughTrace
public import LovaszTheta.TraceBlockTypes

/-!
# The uncolored trace expansion

The trace of a power expands over cyclic sequences of blocks.
Independent sign averaging keeps just the sequences with even
multiplicity at every labeled edge.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Independent

variable {J V : Type*} [Fintype J] [Fintype V]

/-- A choice of basic shape in a family and its vertex labeling. -/
abbrev BasicLabeling (α : J → BasicShape) (V : Type*) :=
  Σ j : J, Fin (α j).toShape.vertexCount ↪ V

namespace BasicLabeling

variable {α : J → BasicShape}

/-- The labeled block represented by the family index and the embedding. -/
def block (f : BasicLabeling α V) : LabeledBlock V := ⟨α f.1,f.2⟩

/-- The signs contributing to the labeled block. -/
noncomputable def edges (f : BasicLabeling α V) : Finset (EdgeIndex V) :=
  labelledEdges (α f.1).toShape f.2

omit [Fintype J] [Fintype V] in
lemma mem_edges_iff {f : BasicLabeling α V} (e : EdgeIndex V) :
    e ∈ f.edges ↔ e.val ∈ f.block.graph.edgeSet := by
  rw [edges,labelledEdges,mem_map,block,LabeledBlock.graph,SimpleGraph.edgeSet_map]
  simp only [Set.mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q.val,q.property,congrArg Subtype.val hq⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨⟨q,hq⟩,Subtype.ext he⟩

end BasicLabeling

/-- A weighted combination of finitely many basic graph matrices. -/
noncomputable def basicCombination (α : J → BasicShape) (a : J → ℝ)
    (x : EdgeIndex V → Bool) : Matrix V V ℝ :=
  ∑ j, a j • graphMatrix (α j).toShape x

private lemma basicCombination_apply (α : J → BasicShape) (a : J → ℝ)
    (x : EdgeIndex V → Bool) (i j : V) :
    basicCombination α a x i j = ∑ f : BasicLabeling α V,
      if f.block.left = i ∧ f.block.right = j then a f.1*walsh f.edges x else 0 := by
  let g (k : J) (f : Fin (α k).toShape.vertexCount ↪ V) : ℝ :=
    if f (α k).toShape.left = i ∧ f (α k).toShape.right = j
    then a k*walsh (labelledEdges (α k).toShape f) x else 0
  calc
    _ = ∑ k, ∑ f, g k f := by
      simp only [g,basicCombination,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,graphMatrix,mul_sum,mul_ite,mul_zero]
    _ = ∑ f : BasicLabeling α V, g f.1 f.2 := (Fintype.sum_sigma' g).symm
    _ = _ := rfl

variable {α : J → BasicShape} {k : ℕ}

/-- The consecutive boundary labels agree, including the closing step. -/
def stitched (f : Fin k → BasicLabeling α V) : Prop :=
  ∀ i, (f i).block.right = (f (finRotate k i)).block.left

/-- Every edge is used an even number of times. -/
def evenEdgeMultiplicity (f : Fin k → BasicLabeling α V) : Prop :=
  ∀ e : EdgeIndex V, Even ((univ.filter fun i ↦ e ∈ (f i).edges).card)

omit [Fintype J] [Fintype V] in
private lemma trace_entry_iff (f : Fin k → BasicLabeling α V) (z : Fin k → V) :
    (∀ i, (f i).block.left = z i ∧ (f i).block.right = z (finRotate k i)) ↔
      stitched f ∧ z = fun i ↦ (f i).block.left := by
  constructor
  · intro h
    exact ⟨fun i ↦ (h i).2.trans (h _).1.symm,funext (fun i ↦ (h i).1.symm)⟩
  · rintro ⟨h,rfl⟩ i
    exact ⟨rfl,h i⟩

private lemma trace_basicCombination_pow_eq_sum (a : J → ℝ) (x : EdgeIndex V → Bool) (k : ℕ) :
    (basicCombination α a x ^ (k+1)).trace =
      ∑ f : Fin (k+1) → BasicLabeling α V, if stitched f then
        (∏ i, a (f i).1*walsh (f i).edges x) else 0 := by
  rw [trace_pow_succ_eq_sum_cycle]
  simp_rw [basicCombination_apply,Fintype.prod_sum]
  have hProd (z : Fin (k+1) → V) (f : Fin (k+1) → BasicLabeling α V) :
      (∏ i, if (f i).block.left = z i ∧ (f i).block.right = z (finRotate (k+1) i)
        then a (f i).1*walsh (f i).edges x else 0) =
      if stitched f ∧ z = fun i ↦ (f i).block.left then
        (∏ i, a (f i).1*walsh (f i).edges x) else 0 := by
    split_ifs with h
    · exact prod_congr rfl fun i _ ↦ ite_eq_left ((trace_entry_iff f z).mpr h i)
    · have hN : ¬∀ i, (f i).block.left = z i ∧ (f i).block.right = z (finRotate (k+1) i) :=
        fun h' ↦ h ((trace_entry_iff f z).mp h')
      rw [not_forall] at hN
      obtain ⟨i,hi⟩ := hN
      exact prod_eq_zero (mem_univ _) (ite_eq_right hi)
  simp_rw [hProd]
  rw [sum_comm]
  apply sum_congr rfl
  intro f _
  by_cases h : stitched f
  · simp [h]
  · simp [h]

/-- The weighted trace moment is the sum over stitched words with even edge multiplicities. -/
theorem average_trace_basicCombination_pow (a : J → ℝ) (k : ℕ) :
    average (fun x : EdgeIndex V → Bool ↦ (basicCombination α a x ^ (k+1)).trace) =
      ∑ f : Fin (k+1) → BasicLabeling α V, if stitched f ∧ evenEdgeMultiplicity f
      then ∏ i, a (f i).1 else 0 := by
  simp_rw [trace_basicCombination_pow_eq_sum,average_sum]
  apply sum_congr rfl
  intro f _
  by_cases h : stitched f
  · simp only [h,ite_true,true_and,prod_mul_distrib,average_mul_left]
    rw [average_walsh_prod]
    unfold evenEdgeMultiplicity
    split_ifs <;> simp
  · simp [h]

/-- The stitched labeled blocks used in the sharp count. -/
def toTraceBlocks (f : Fin k → BasicLabeling α V) (hf : stitched f) : TraceBlocks V k :=
  ⟨fun i ↦ (f i).block,hf⟩

omit [Fintype J] [Fintype V] in
lemma repeatedEdges_of_evenEdgeMultiplicity (f : Fin k → BasicLabeling α V) (hf : stitched f)
    (hEven : evenEdgeMultiplicity f) : (toTraceBlocks f hf).RepeatedEdges := by
  intro i u v h
  let e : EdgeIndex V := ⟨s(u,v),fun he ↦ h.ne (Sym2.mk_isDiag_iff.mp he)⟩
  let S := univ.filter fun j ↦ e ∈ (f j).edges
  have hI : i ∈ S := mem_filter.mpr ⟨mem_univ _,
    (BasicLabeling.mem_edges_iff e).mpr (by exact h)⟩
  by_contra! hn
  have hS : S = {i} := by
    ext j
    constructor
    · intro hj
      apply mem_singleton.mpr
      by_contra he
      exact hn j he ((BasicLabeling.mem_edges_iff e).mp (mem_filter.mp hj).2)
    · rw [mem_singleton]
      rintro rfl
      exact hI
  have hE : Even S.card := hEven e
  rw [hS,card_singleton] at hE
  exact (by decide : ¬Even (1 : ℕ)) hE

end LovaszTheta.Independent
