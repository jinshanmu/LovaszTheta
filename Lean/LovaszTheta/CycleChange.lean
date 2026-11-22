module

public import LovaszTheta.PairCoordinates
public import LovaszTheta.TraceReturnPrefix

/-!
# Injective relabeling of return shapes

The starting side and the destination choice specify the cycle
permutation. For fixed choices, the return graph determines the
forward graph and the forward graph determines the return graph.
-/

@[expose] public section

open SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

/-- Which forward endpoint starts the return, and whether the destination is the other one. -/
structure BoundaryChange where
  /-- Whether the return starts at the original left endpoint. -/
  fromLeft : Bool
  /-- Whether the destination is the other original endpoint. -/
  toOther : Bool

/-- The return's fixed permutation of the original block coordinates. -/
def BoundaryChange.frame (a : BoundaryChange) (n : ℕ) : Equiv.Perm (Fin (n+2)) :=
  cycleFrame (if a.fromLeft then 0 else 1)
    (if a.fromLeft then if a.toOther then 1 else -1 else if a.toOther then 0 else 1+1)

namespace LabeledBlock

variable {V : Type*}

/-- The boundary decisions of a labeled return. -/
noncomputable def boundaryChange (b c : LabeledBlock V) : BoundaryChange :=
  ⟨decide (c.left = b.left),decide (c.right = TraceBlocks.otherEndpoint b c.left)⟩

lemma label_pairedCyclePermutation_left (b c : LabeledBlock V) (h : b.graph = c.graph) :
    b.label (pairedCyclePermutation b c h 0) = c.left := by
  unfold pairedCyclePermutation
  have hEq : finCongr (congrArg (·+2) (additionalVertices_eq_of_graph_eq h)) 0 = 0 := Fin.ext rfl
  rw [Equiv.trans_apply,hEq,label_changeCoordinates]
  rfl

lemma label_pairedCyclePermutation_right (b c : LabeledBlock V) (h : b.graph = c.graph) :
    b.label (pairedCyclePermutation b c h 1) = c.right := by
  unfold pairedCyclePermutation
  have hEq : finCongr (congrArg (·+2) (additionalVertices_eq_of_graph_eq h)) 1 = 1 := by
    apply Fin.ext
    simp
  rw [Equiv.trans_apply,hEq,label_changeCoordinates]
  rfl

lemma label_pairedCyclePermutation_apply (b c : LabeledBlock V) (h : b.graph = c.graph)
    (i : Fin (b.shape.additionalVertices+2)) :
    b.label (pairedCyclePermutation b c h i) =
      c.label (finCongr (congrArg (·+2) (additionalVertices_eq_of_graph_eq h)) i) :=
  label_changeCoordinates b c h _

/-- The equality of the labeled graph fixes the permutation once the two decisions have been recorded. -/
theorem pairedCyclePermutation_eq_change (b c : LabeledBlock V) (h : b.graph = c.graph)
    (hStart : c.left = b.left ∨ c.left = b.right) :
    pairedCyclePermutation b c h = (b.boundaryChange c).frame b.shape.additionalVertices := by
  let e := pairedCyclePermutation b c h
  have hLeft : b.label (e 0) = c.left := label_pairedCyclePermutation_left b c h
  have hRight : b.label (e 1) = c.right := label_pairedCyclePermutation_right b c h
  have hAdj := pairedCyclePermutation_eq_frame b c h
  have hIv : (cycleGraph (b.shape.additionalVertices+2)).Adj (e 0) (e 1) := by
    have hE : (cycleGraph (b.shape.additionalVertices+2)).Adj (0 : Fin (b.shape.additionalVertices+2)) 1 :=
      cycleGraph_adj.mpr (Or.inr (sub_zero 1))
    have hE' := (cycleFrame_adj_iff (e 0) (e 1) 0 1).mpr hE
    rw [← hAdj] at hE'
    exact hE'
  change e = _
  refine hAdj.trans ?_
  unfold BoundaryChange.frame boundaryChange
  by_cases hs : c.left = b.left
  · have h₀ : e 0 = 0 := b.label.injective (hLeft.trans hs)
    rw [h₀]
    simp only [decide_eq_true_eq,hs,ite_true,TraceBlocks.otherEndpoint]
    by_cases ht : c.right = b.right
    · have h₁ : e 1 = 1 := b.label.injective (hRight.trans ht)
      rw [h₁,ite_eq_left ht]
    · have hNe : e 1 ≠ 1 := fun he ↦ ht (by rw [← hRight,he]; rfl)
      rw [h₀] at hIv
      rcases cycleGraph_adj.mp hIv with h1 | h2
      · have hNeg : -(e 1) = 1 := by simpa only [zero_sub] using h1
        have h₁ : e 1 = -1 := (neg_neg (e 1)).symm.trans (congrArg Neg.neg hNeg)
        rw [h₁,ite_eq_right ht]
      · exact (hNe (by simpa only [sub_zero] using h2)).elim
  · have h₀ : e 0 = 1 := b.label.injective (hLeft.trans (hStart.resolve_left hs))
    rw [h₀]
    simp only [decide_eq_true_eq,hs,ite_false,TraceBlocks.otherEndpoint]
    by_cases ht : c.right = b.left
    · have h₁ : e 1 = 0 := b.label.injective (hRight.trans ht)
      rw [h₁,ite_eq_left ht]
    · have hNe : e 1 ≠ 0 := fun he ↦ ht (by rw [← hRight,he]; rfl)
      rw [h₀] at hIv
      rcases cycleGraph_adj.mp hIv with h1 | h2
      · have h₁ : e 1 = 0 := by
          calc
            _ = 1-(1-e 1) := by abel
            _ = _ := by rw [h1,sub_self]
        exact (hNe h₁).elim
      · have h₁ : e 1 = 1+1 := (sub_eq_iff_eq_add.mp h2)
        rw [h₁,ite_eq_right ht]

end LabeledBlock

/-- The return graph relation in the two canonical cycle coordinate systems. -/
def InReturnFrame (a : BoundaryChange) (S T : BasicShape) : Prop :=
  ∃ h : S.additionalVertices = T.additionalVertices, ∀ i j : Fin (S.additionalVertices+2),
    T.graph.Adj (finCongr (congrArg (·+2) h) i) (finCongr (congrArg (·+2) h) j) ↔
      S.graph.Adj (a.frame S.additionalVertices i) (a.frame S.additionalVertices j)

theorem LabeledBlock.inReturnFrame_of_graph_eq {V : Type*} (b c : LabeledBlock V) (h : b.graph = c.graph)
    (hStart : c.left = b.left ∨ c.left = b.right) :
    InReturnFrame (b.boundaryChange c) b.shape c.shape := by
  refine ⟨additionalVertices_eq_of_graph_eq h,fun i j ↦ ?_⟩
  rw [← pairedCyclePermutation_eq_change b c h hStart]
  exact (pairedCyclePermutation_adj_iff b c h i j).symm

lemma InReturnFrame.right_unique {a : BoundaryChange} {S T U : BasicShape}
    (hT : InReturnFrame a S T) (hU : InReturnFrame a S U) : T = U := by
  obtain ⟨n,G,hG,hN⟩ := S
  obtain ⟨m,H,hH,hM⟩ := T
  obtain ⟨k,J,hJ,hK⟩ := U
  obtain ⟨hnM,hT⟩ := hT
  obtain ⟨hnK,hU⟩ := hU
  change n = m at hnM
  change n = k at hnK
  subst m
  subst k
  have he : H = J := by
    ext i j
    exact (hT i j).trans (hU i j).symm
  subst J
  rfl

lemma InReturnFrame.left_unique {a : BoundaryChange} {S T U : BasicShape}
    (hS : InReturnFrame a S U) (hT : InReturnFrame a T U) : S = T := by
  obtain ⟨n,G,hG,hN⟩ := S
  obtain ⟨m,H,hH,hM⟩ := T
  obtain ⟨k,J,hJ,hK⟩ := U
  obtain ⟨hnK,hS⟩ := hS
  obtain ⟨hmK,hT⟩ := hT
  change n = k at hnK
  change m = k at hmK
  subst n
  subst m
  have he : G = H := by
    ext i j
    let x := (a.frame k).symm i
    let y := (a.frame k).symm j
    have hEq := (hS x y).symm.trans (hT x y)
    change G.Adj (a.frame k x) (a.frame k y) ↔ H.Adj (a.frame k x) (a.frame k y) at hEq
    simpa only [x,y,Equiv.apply_symm_apply] using hEq
  subst H
  rfl

end LovaszTheta.Independent
