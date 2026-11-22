module

public import LovaszTheta.CoefficientApproximation

/-!
# Reading the coefficient arrays as graph matrices

The array of new coefficients is precisely the sum of closed
chains and the padded array is the old matrix combination.
Their difference gives the matrix error controlled by the sharp
norm estimate.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.Construction

variable {N : ℕ}

/-- The weighted matrix combination at the specified depth. -/
noncomputable def combination (N h : ℕ) : MatrixFamily :=
  blockCombination (shape N h) (normalized N h)

/-- The weighted single chains from the same coefficient array. -/
noncomputable def chains (N h j : ℕ) : MatrixFamily :=
  chainSum (shape N h) (normalized N h) j

private lemma blockCombination_closedCoefficient (N h : ℕ) :
    blockCombination (shape N (h+1)) (closedCoefficient N h) =
      ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j • closeEntries (chains N h j) := by
  let J := nonlinearDegrees N
  let β := shape N (h+1)
  let c := closedCoefficient N h
  let F (j : J) (w : Fin j.val → Construction N h) : MatrixFamily :=
    c (node h j w) • blockFamily (β (node h j w))
  unfold blockCombination
  change (∑ t : Unit ⊕ (Σ j : J, Fin j.val → Construction N h), c t • blockFamily (β t)) = _
  rw [Fintype.sum_sum_type]
  have hLeaf : (∑ t : Unit, c (Sum.inl t) • blockFamily (β (Sum.inl t))) = 0 := by
    simp only [c,closedCoefficient,zero_smul,sum_const_zero]
  rw [hLeaf,zero_add]
  have hSigma :
      (∑ t : (Σ j : J, Fin j.val → Construction N h), c (Sum.inr t) • blockFamily (β (Sum.inr t))) =
        ∑ j : J, ∑ w, F j w := by
    calc
      _ = ∑ t : (Σ j : J, Fin j.val → Construction N h), F t.1 t.2 :=
        sum_congr rfl fun t _ ↦ by cases t; rfl
      _ = _ := Fintype.sum_sigma' F
  rw [hSigma,← sum_coe_sort J (fun j ↦ bernsteinCoefficient N j • closeEntries (chains N h j))]
  apply sum_congr rfl
  intro j _
  change (∑ w, F j w) =
    bernsteinCoefficient N j.val • closeEntries (∑ w : Fin j.val → Construction N h,
      wordWeight (normalized N h) w • chainFamily (wordChain (shape N h) w))
  rw [map_sum,smul_sum]
  apply sum_congr rfl
  intro w _
  let C := wordChain (shape N h) w
  have hL : 2 ≤ C.length := by
    unfold C wordChain
    rw [List.length_ofFn]
    exact arity_ge_two j
  change (bernsteinCoefficient N j.val * wordWeight (normalized N h) w) •
    blockFamily (C.close (chain_ofFn_nonempty j _)) =
      bernsteinCoefficient N j.val • closeEntries (wordWeight (normalized N h) w • chainFamily C)
  rw [map_smul,closeEntries_chainFamily C (chain_ofFn_nonempty j _) hL,smul_smul]

private lemma blockCombination_paddedCoefficient (N h : ℕ) :
    blockCombination (shape N (h+1)) (paddedCoefficient N h) = combination N h := by
  unfold blockCombination
  simp only [paddedCoefficient,ite_smul,zero_smul,← sum_filter,filter_mem_eq_inter,univ_inter]
  rw [previousTrees,sum_image (widen_injective N h).injOn]
  simp only [shape_widen,coefficient_widen,combination,blockCombination,normalized]

private lemma blockCombination_leafCoefficient (N h : ℕ) :
    blockCombination (shape N (h+1)) (leafCoefficient N h) =
      normalized N h (leaf h) • blockFamily singleEdgeShape := by
  simp only [blockCombination,leafCoefficient,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,shape_leaf]

/-- The matrix of the coefficient difference is the error between
the closure construction and the previous weighted matrix. -/
theorem blockCombination_difference (N h : ℕ) :
    blockCombination (shape N (h+1)) (difference N h) =
      (∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j • closeEntries (chains N h j)) +
        normalized N h (leaf h) • blockFamily singleEdgeShape - combination N h := by
  have hAdd :
      blockCombination (shape N (h+1)) (difference N h) =
        blockCombination (shape N (h+1)) (closedCoefficient N h) +
          blockCombination (shape N (h+1)) (leafCoefficient N h) -
            blockCombination (shape N (h+1)) (paddedCoefficient N h) := by
    simp only [blockCombination,difference,sub_smul,add_smul,sum_sub_distrib,sum_add_distrib]
  rw [hAdd,blockCombination_closedCoefficient,blockCombination_leafCoefficient,
    blockCombination_paddedCoefficient]

end LovaszTheta.Independent.Construction
