module

public import LovaszTheta.ChainBasics
public import Mathlib.Data.List.OfFn

/-!
# Weighted sums of chains

The appending rule adds a new independent block index. Backtracking
removes the last block and sums the product of its coefficient and
that of its reversal. This sum is one for a symmetric array of
squared norm one.
-/

@[expose] public section

open Finset
open scoped Classical Matrix Matrix.Norms.L2Operator

namespace LovaszTheta.Independent

variable {J : Type*} [Fintype J]

/-- The product coefficient of an ordered chain of indices. -/
noncomputable def wordWeight (c : J → ℝ) {j : ℕ} (w : Fin j → J) : ℝ := ∏ i, c (w i)

/-- The chain specified by a word of shape indices. -/
def wordChain (α : J → BasicShape) {j : ℕ} (w : Fin j → J) : Chain := List.ofFn (fun i ↦ α (w i))

/-- The weighted sum of chains of a specified length. -/
noncomputable def chainSum (α : J → BasicShape) (c : J → ℝ) (j : ℕ) : MatrixFamily :=
  ∑ w : Fin j → J, wordWeight c w • chainFamily (wordChain α w)

/-- The weighted sum of normalized basic blocks. -/
noncomputable def blockCombination (α : J → BasicShape) (c : J → ℝ) : MatrixFamily :=
  ∑ j, c j • blockFamily (α j)

lemma blockCombination_apply_eq (α : J → BasicShape) (c : J → ℝ) (n : ℕ) (x : SignSample n) :
    blockCombination α c n x = normalizedCombination α c x := by
  simp only [blockCombination,normalizedCombination,basicCombination,Finset.sum_apply,Pi.smul_apply,
    blockFamily,ChainTerm.blockMatrix,smul_smul,chainNormalization]
  apply sum_congr rfl
  intro j _
  have he : -((α j).span : ℝ)/2 = -(((α j).toShape.vertexCount : ℝ)-1)/2 := by
    change -(((α j).additionalVertices+1 : ℕ) : ℝ)/2 =
      -((((α j).additionalVertices+2 : ℕ) : ℝ)-1)/2
    push_cast
    ring
  rw [he]

lemma sum_words_cons {A : Type*} [AddCommMonoid A] {j : ℕ} (f : (Fin (j+1) → J) → A) :
    (∑ w, f w) = ∑ a, ∑ w : Fin j → J, f (Fin.cons a w) := by
  rw [← Fintype.sum_prod_type' (fun a (w : Fin j → J) ↦ f (Fin.cons a w))]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (j+1) ↦ J)) _ f (fun aw ↦ rfl)).symm

omit [Fintype J] in
lemma wordWeight_cons (c : J → ℝ) {j : ℕ} (a : J) (w : Fin j → J) :
    wordWeight c (Fin.cons a w) = c a * wordWeight c w := by
  rw [wordWeight,Fin.prod_univ_succ]
  rfl

omit [Fintype J] in
lemma wordChain_cons (α : J → BasicShape) {j : ℕ} (a : J) (w : Fin j → J) :
    wordChain α (Fin.cons a w) = α a :: wordChain α w := by
  rw [wordChain,List.ofFn_succ]
  rfl

lemma chainSum_succ (α : J → BasicShape) (c : J → ℝ) (j : ℕ) :
    chainSum α c (j+1) = ∑ a, ∑ w : Fin j → J,
      (c a * wordWeight c w) • chainFamily (α a :: wordChain α w) := by
  rw [chainSum,sum_words_cons]
  simp only [wordWeight_cons,wordChain_cons]

lemma chainSum_zero (α : J → BasicShape) (c : J → ℝ) : chainSum α c 0 = 1 := by
  unfold chainSum
  rw [Fintype.sum_unique]
  simp [wordWeight,wordChain,chainFamily_nil]

lemma chainSum_one (α : J → BasicShape) (c : J → ℝ) : chainSum α c 1 = blockCombination α c := by
  rw [show (1 : ℕ) = 0+1 by rfl,chainSum_succ,blockCombination]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_unique]
  simp [wordWeight,wordChain,chainFamily_singleton]

private lemma mul_smul_family (A B : MatrixFamily) (r : ℝ) : A*(r • B) = r • (A*B) := by
  funext n x
  exact Matrix.mul_smul (A n x) r (B n x)

/-- Multiplying a remainder by the weighted sum still gives a remainder
on the event where the weighted sum has bounded norm. -/
theorem chainRemainders_mul_blockCombination_mem (α : J → BasicShape) (c : J → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hBound : WithHighProbability (fun n x ↦ ‖blockCombination α c n x‖ ≤ K))
    {A : MatrixFamily} (hA : A ∈ chainRemainders) :
    A * blockCombination α c ∈ chainRemainders := by
  obtain ⟨P,hP,E,hE,rfl⟩ := Submodule.mem_sup.mp hA
  rw [add_mul]
  apply Submodule.add_mem
  · rw [blockCombination,mul_sum]
    apply Submodule.sum_mem
    intro j _
    rw [mul_smul_family]
    exact Submodule.smul_mem _ _ (pairSpace_mul_blockFamily_mem hP (α j))
  · exact (le_sup_right : errorSpace ≤ chainRemainders) (NormVanishes.mul_right hE hK hBound)

/-- The weighted chain recurrence modulo two-chain terms and errors. -/
theorem chainSum_mul_sub_append_sub_backtrack_mem (α : J → BasicShape) (c : J → ℝ)
    (hα : Function.Injective α) (r : Equiv.Perm J)
    (hShape : ∀ a, α (r a) = (α a).reverse) (hWeight : ∀ a, c (r a) = c a)
    (hc : ∑ a, (c a)^2 = 1) (j : ℕ) :
    chainSum α c (j+1) * blockCombination α c - chainSum α c (j+2) -
      chainSum α c j ∈ chainRemainders := by
  let C (a : J) (w : Fin j → J) := chainFamily (α a :: wordChain α w)
  let B (s : J) := blockFamily (α s)
  let X (a : J) (w : Fin j → J) (s : J) := chainFamily (α s :: α a :: wordChain α w)
  let Y (a : J) (w : Fin j → J) (s : J) :=
    if α s = (α a).reverse then chainFamily (wordChain α w) else 0
  let g (a : J) (w : Fin j → J) (s : J) := c a*wordWeight c w*c s
  have hMul : chainSum α c (j+1)*blockCombination α c =
      ∑ a, ∑ w : Fin j → J, ∑ s, g a w s • (C a w * B s) := by
    rw [chainSum_succ,blockCombination,sum_mul]
    simp only [sum_mul,mul_sum,smul_mul_assoc,mul_smul_family,smul_smul,C,B,g]
    exact sum_congr rfl (fun _ _ ↦ sum_comm)
  have hAppend : chainSum α c (j+2) = ∑ a, ∑ w : Fin j → J, ∑ s, g a w s • X a w s := by
    unfold chainSum
    rw [sum_words_cons]
    simp only [wordWeight_cons,wordChain_cons]
    simp_rw [sum_words_cons (j := j),wordWeight_cons,wordChain_cons]
    have he : (∑ a, ∑ w : Fin j → J, ∑ s, g a w s • X a w s) =
        ∑ s, ∑ a, ∑ w : Fin j → J, g a w s • X a w s := by
      calc
        _ = ∑ a, ∑ s, ∑ w : Fin j → J, g a w s • X a w s :=
          sum_congr rfl (fun _ _ ↦ sum_comm)
        _ = _ := sum_comm
    rw [he]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro w _
    congr 1
    unfold g
    ring
  have hBackAt (a : J) (w : Fin j → J) :
      (∑ s, g a w s • Y a w s) = (c a)^2 • (wordWeight c w • chainFamily (wordChain α w)) := by
    have hY (s : J) : α s = (α a).reverse ↔ s = r a := by rw [← hShape a]; exact hα.eq_iff
    simp only [g,Y,hY,smul_ite,smul_zero,sum_ite_eq',mem_univ,ite_true,hWeight,smul_smul]
    congr 1
    ring
  have hBack : chainSum α c j = ∑ a, ∑ w : Fin j → J, ∑ s, g a w s • Y a w s := by
    simp_rw [hBackAt,← smul_sum,← sum_smul,hc,one_smul]
    rfl
  rw [hMul,hAppend,hBack,← sum_sub_distrib,← sum_sub_distrib]
  apply Submodule.sum_mem
  intro a _
  simp only [← sum_sub_distrib,← smul_sub]
  apply Submodule.sum_mem
  intro w _
  apply Submodule.sum_mem
  intro s _
  apply Submodule.smul_mem
  exact chainFamily_mul_blockFamily_sub_append_sub_backtrack_mem (wordChain α w) (α a) (α s)

end LovaszTheta.Independent
