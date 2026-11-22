module

public import LovaszTheta.WeightedChains
public import LovaszTheta.SemicircleChebyshev

/-!
# The Chebyshev recurrence for graph matrices

On the sharp norm event, multiplying an error by the block
combination preserves its vanishing norm. The chain recurrence
therefore gives the Chebyshev polynomial as a single-chain sum,
a finite pair combination, and a vanishing error.
-/

@[expose] public section

open Finset Filter Matrix Polynomial
open scoped Classical Matrix Matrix.Norms.L2Operator Polynomial Topology

namespace LovaszTheta.Independent

variable {J : Type*} [Fintype J]

lemma blockFamily_reverse (T : BasicShape) (n : ℕ) (x : SignSample n) :
    blockFamily T.reverse n x = (blockFamily T n x)ᵀ := by
  unfold blockFamily ChainTerm.blockMatrix
  rw [T.reverseIsomorphism.graphMatrix_eq,graphMatrix_reverse,Matrix.transpose_smul]
  rfl

/-- A reversal-invariant coefficient array yields symmetric matrices. -/
theorem blockCombination_isSymm (α : J → BasicShape) (c : J → ℝ) (r : Equiv.Perm J)
    (hShape : ∀ j, α (r j) = (α j).reverse) (hc : ∀ j, c (r j) = c j)
    (n : ℕ) (x : SignSample n) : (blockCombination α c n x).IsSymm := by
  change (blockCombination α c n x)ᵀ = _
  simp only [blockCombination,Finset.sum_apply,Pi.smul_apply,Matrix.transpose_sum,Matrix.transpose_smul]
  exact Fintype.sum_equiv r _ _ fun j ↦ by rw [hc,hShape,blockFamily_reverse]

/-- The sharp bound as a high-probability event for the weighted combination. -/
theorem withHighProbability_blockCombination (α : J → BasicShape) (c : J → ℝ)
    (hα : Function.Injective α) (r : Equiv.Perm J)
    (hShape : ∀ j, α (r j) = (α j).reverse) (hc : ∀ j, c (r j) = c j)
    {ε : ℝ} (hε : 0 < ε) :
    WithHighProbability (fun n x ↦ ‖blockCombination α c n x‖ ≤
      (2+ε)*Real.sqrt (∑ j, (c j)^2)) := by
  have hs n x : (normalizedCombination α c (n := n) x).IsSymm := by
    rw [← blockCombination_apply_eq]
    exact blockCombination_isSymm α c r hShape hc n x
  intro m hm
  filter_upwards [eventually_probability_opNorm_normalizedCombination α hα c hs hε hm,
    eventually_ge_atTop (2 : ℕ)] with n he hn
  simp only [not_le,blockCombination_apply_eq]
  have h₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h₀ : (0 : ℝ) < n := by linarith
  refine he.trans ?_
  rw [sub_eq_add_neg,Real.rpow_add h₀,Real.rpow_neg_one]
  have hn' := (div_le_one h₀).mpr h₂
  calc
    _ = (n : ℝ)^(-m)*(2/(n : ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (Real.rpow_nonneg h₀.le _) hn'

/-- Evaluate a real polynomial on each matrix of a family. -/
noncomputable def polynomialFamily (A : MatrixFamily) (p : ℝ[X]) : MatrixFamily :=
  fun n x ↦ Polynomial.aeval (A n x) p

lemma polynomialFamily_one (A : MatrixFamily) : polynomialFamily A 1 = 1 := by
  funext n x
  exact map_one (Polynomial.aeval (A n x))

lemma polynomialFamily_X (A : MatrixFamily) : polynomialFamily A X = A := by
  funext n x
  exact aeval_X _

lemma polynomialFamily_chebyshev_add_two (A : MatrixFamily) (j : ℕ) :
    polynomialFamily A (semicircleChebyshev (j+2)) =
      polynomialFamily A (semicircleChebyshev (j+1))*A - polynomialFamily A (semicircleChebyshev j) := by
  funext n x
  unfold polynomialFamily
  rw [semicircleChebyshev_add_two,mul_comm X,map_sub,map_mul,aeval_X]
  rfl

/-- Each Chebyshev evaluation has the chain expansion of the manuscript. -/
theorem exists_chebyshev_decomposition (α : J → BasicShape) (c : J → ℝ)
    (hα : Function.Injective α) (r : Equiv.Perm J)
    (hShape : ∀ j, α (r j) = (α j).reverse) (hWeight : ∀ j, c (r j) = c j)
    (hc : ∑ j, (c j)^2 = 1) (j : ℕ) :
    ∃ D ∈ pairSpace, ∃ E, NormVanishes E ∧
      polynomialFamily (blockCombination α c) (semicircleChebyshev j) = chainSum α c j + D + E := by
  let M := blockCombination α c
  let P (j : ℕ) := polynomialFamily M (semicircleChebyshev j)
  let C := chainSum α c
  have hNorm : WithHighProbability (fun n x ↦ ‖M n x‖ ≤ 3) := by
    have h := withHighProbability_blockCombination α c hα r hShape hWeight (show (0 : ℝ) < 1 by norm_num)
    simpa only [hc,Real.sqrt_one,mul_one,show (2 : ℝ)+1 = 3 by norm_num] using h
  have hRem (j : ℕ) : P j - C j ∈ chainRemainders := by
    induction j using Nat.twoStepInduction with
    | zero =>
      simp only [P,C,semicircleChebyshev_zero,polynomialFamily_one,chainSum_zero,sub_self]
      exact Submodule.zero_mem _
    | one =>
      simp only [P,C,semicircleChebyshev_one,polynomialFamily_X,chainSum_one,sub_self,M]
      exact Submodule.zero_mem _
    | more j h₀ h₁ =>
      have hR := chainRemainders_mul_blockCombination_mem α c (by norm_num : (0 : ℝ) ≤ 3) hNorm h₁
      have hC := chainSum_mul_sub_append_sub_backtrack_mem α c hα r hShape hWeight hc j
      have h := Submodule.sub_mem _ (Submodule.add_mem _ hR hC) h₀
      have hID : P (j+2)-C (j+2) =
          ((P (j+1)-C (j+1))*M + (C (j+1)*M-C (j+2)-C j))-(P j-C j) := by
        rw [show P (j+2) = P (j+1)*M-P j from polynomialFamily_chebyshev_add_two M j,sub_mul]
        abel
      rw [hID]
      exact h
  obtain ⟨D,hD,E,hE,he⟩ := Submodule.mem_sup.mp (hRem j)
  refine ⟨D,hD,E,hE,?_⟩
  have h : P j - C j = D+E := he.symm
  have h' := congrArg (fun z ↦ C j+z) h
  change P j = C j+D+E
  abel_nf at h' ⊢
  exact h'

end LovaszTheta.Independent
