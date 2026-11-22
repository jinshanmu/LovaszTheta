module

public import LovaszTheta.Backtracking

/-!
# Chain multiplication modulo pairs and errors

The two-chain matrices span a space closed under right block
multiplication up to a vanishing error. For a single chain, the
append and backtrack contributions are kept separately.
-/

@[expose] public section

open Finset Filter
open scoped Classical Matrix Matrix.Norms.L2Operator

namespace LovaszTheta.Independent

/-- The normalized matrix of a single chain as a family in the graph size. -/
noncomputable def chainFamily (C : Chain) : MatrixFamily := fun _ x ↦ (ChainTerm.single C).matrix x

/-- The normalized matrix of a fixed separated pair as a family in the graph size. -/
noncomputable def pairFamily (C : Chain × Chain) : MatrixFamily := fun _ x ↦ (ChainTerm.pair C.1 C.2).matrix x

/-- The normalized matrix of a basic block as a family in the graph size. -/
noncomputable def blockFamily (T : BasicShape) : MatrixFamily := fun _ x ↦ ChainTerm.blockMatrix T x

/-- Finite linear combinations of separated pairs. -/
noncomputable def pairSpace : Submodule ℝ MatrixFamily := Submodule.span ℝ (Set.range pairFamily)

/-- The subspace of families of vanishing operator norm. -/
def errorSpace : Submodule ℝ MatrixFamily where
  carrier := {A | NormVanishes A}
  zero_mem' := NormVanishes.of_zero
  add_mem' := NormVanishes.add
  smul_mem' r _ h := h.smul r

/-- Two-chain terms and operator-norm errors. -/
noncomputable def chainRemainders : Submodule ℝ MatrixFamily := pairSpace ⊔ errorSpace

lemma pairFamily_mem (C : Chain × Chain) : pairFamily C ∈ pairSpace :=
  Submodule.subset_span (Set.mem_range_self C)

private lemma matrix_mem_pairSpace (P : ChainTerm) (h : P.leftChain.isSome) :
    (fun n x ↦ P.matrix (n := n) x) ∈ pairSpace := by
  obtain ⟨L,C⟩ := P
  have he : L.isSome := h
  obtain ⟨P,hP⟩ := Option.isSome_iff_exists.mp he
  subst L
  exact pairFamily_mem (P,C)

private lemma output_mem_pair (out : Option ChainTerm)
    (h : ∀ P, out = some P → P.leftChain.isSome) :
    (fun n x ↦ ChainTerm.outputMatrix out n x) ∈ pairSpace := by
  cases out with
  | none => exact Submodule.zero_mem _
  | some P => exact matrix_mem_pairSpace P (h P rfl)

private lemma remainder_mem (A B : MatrixFamily) (hB : B ∈ pairSpace)
    (h : NormVanishes (A-B)) : A ∈ chainRemainders :=
  Submodule.mem_sup.mpr ⟨B,hB,A-B,h,by abel⟩

private lemma pair_mul_block_empty (C : Chain) (S : BasicShape) :
    pairFamily (C,[]) * blockFamily S ∈ chainRemainders := by
  let P := ChainTerm.pair C []
  apply remainder_mem (B := fun n x ↦ ∑ p, ChainTerm.outputMatrix (P.emptyProductOutput S p) n x)
  · have hSum (p : Identification P.toShape S.toShape) :
        (fun n x ↦ ChainTerm.outputMatrix (P.emptyProductOutput S p) n x) ∈ pairSpace := by
      apply output_mem_pair
      intro Q hq
      unfold ChainTerm.emptyProductOutput at hq
      split_ifs at hq
      have hEq := Option.some.inj hq
      subst Q
      rfl
    have he := Submodule.sum_mem pairSpace (t := univ) (fun p _ ↦ hSum p)
    convert he using 1
    funext n x
    simp only [Finset.sum_apply]
  · exact P.normVanishes_empty_product S rfl

private lemma pair_mul_block_cons (C D : Chain) (T S : BasicShape) :
    pairFamily (C,T::D) * blockFamily S ∈ chainRemainders := by
  let P := ChainTerm.pair C D
  apply remainder_mem (B := fun n x ↦ ∑ p, ChainTerm.outputMatrix (P.nonemptyProductOutput T S p) n x)
  · have hSum (p : Identification (P.append T).toShape S.toShape) :
        (fun n x ↦ ChainTerm.outputMatrix (P.nonemptyProductOutput T S p) n x) ∈ pairSpace := by
      apply output_mem_pair
      intro Q hq
      unfold ChainTerm.nonemptyProductOutput at hq
      split_ifs at hq
      · have hEq := Option.some.inj hq
        subst Q
        rfl
      · unfold ChainTerm.cancellationOutput at hq
        have hL : P.leftChain ≠ none := by simp [P]
        rw [ite_eq_right hL] at hq
        split_ifs at hq <;> exact (Option.some.inj hq) ▸ (show P.leftChain.isSome from rfl)
    have he := Submodule.sum_mem pairSpace (t := univ) (fun p _ ↦ hSum p)
    convert he using 1
    funext n x
    simp only [Finset.sum_apply]
  · exact P.normVanishes_nonempty_product T S

lemma pairFamily_mul_blockFamily_mem (C : Chain × Chain) (S : BasicShape) :
    pairFamily C * blockFamily S ∈ chainRemainders := by
  obtain ⟨L,R⟩ := C
  cases R with
  | nil => exact pair_mul_block_empty L S
  | cons T R => exact pair_mul_block_cons L R T S

/-- Finite combinations of pairs stay in the remainder space after block multiplication. -/
theorem pairSpace_mul_blockFamily_mem {B : MatrixFamily} (hB : B ∈ pairSpace) (S : BasicShape) :
    B * blockFamily S ∈ chainRemainders := by
  induction hB using Submodule.span_induction with
  | mem B h =>
    obtain ⟨C,rfl⟩ := h
    exact pairFamily_mul_blockFamily_mem C S
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add A B _ _ hA hB =>
    rw [add_mul]
    exact Submodule.add_mem _ hA hB
  | smul r A _ hA =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ hA

private lemma single_output_mem (C : Chain) (T S : BasicShape)
    (p : Identification ((ChainTerm.single C).append T).toShape S.toShape)
    (hf : p ≠ Identification.fresh ((ChainTerm.single C).append T).toShape S.toShape)
    (hn : ¬(p.newGraph = (ChainTerm.single C).lastGraph T S p ∧
      p.outputRight = (ChainTerm.single C).junction T S p)) :
    (fun n x ↦ ChainTerm.outputMatrix ((ChainTerm.single C).nonemptyProductOutput T S p) n x) ∈ pairSpace := by
  apply output_mem_pair
  intro Q hQ
  unfold ChainTerm.nonemptyProductOutput at hQ
  rw [ite_eq_right hf] at hQ
  split_ifs at hQ with h
  have hW := fun h' ↦ hn ⟨h,h'⟩
  unfold ChainTerm.cancellationOutput at hQ
  rw [ite_eq_right hW,ite_eq_left rfl] at hQ
  have hEq := Option.some.inj hQ
  subst Q
  rfl

/-- A single-chain product has an append term, one backtrack for the
reversed block, and a remainder of pairs and errors. -/
theorem chainFamily_mul_blockFamily_sub_append_sub_backtrack_mem (C : Chain) (T S : BasicShape) :
    chainFamily (T::C) * blockFamily S - chainFamily (S::T::C) -
      (if S = T.reverse then chainFamily C else 0) ∈ chainRemainders := by
  let P := ChainTerm.single C
  let f (p : Identification (P.append T).toShape S.toShape) : MatrixFamily :=
    fun n x ↦ ChainTerm.outputMatrix (P.nonemptyProductOutput T S p) n x
  let p₀ := Identification.fresh (P.append T).toShape S.toShape
  let A := chainFamily (S::T::C)
  have hAppend : f p₀ = A := by
    funext n x
    change ChainTerm.outputMatrix (P.nonemptyProductOutput T S p₀) n x = _
    unfold ChainTerm.nonemptyProductOutput p₀
    simp [ChainTerm.outputMatrix,A,chainFamily,P,ChainTerm.append]
  have hErr : chainFamily (T::C)*blockFamily S - (∑ p, f p) ∈ errorSpace := by
    change NormVanishes _
    have h := P.normVanishes_nonempty_product T S
    apply h.congr
    exact Eventually.of_forall (fun n x ↦ by
      simp only [Pi.sub_apply,Pi.mul_apply,Finset.sum_apply]
      rfl)
  have hRemaining :
      (∑ p, f p) - A - (if S = T.reverse then chainFamily C else 0) ∈ pairSpace := by
    by_cases hS : S = T.reverse
    · subst S
      rw [ite_eq_left rfl]
      let p₁ := P.backtrackIdentification T
      have hNe : p₁ ≠ p₀ := P.backtrack_ne_fresh T
      have hBack : f p₁ = chainFamily C := by
        funext n x
        unfold f ChainTerm.nonemptyProductOutput
        rw [ite_eq_right hNe,ite_eq_left (P.backtrack_newGraph T)]
        unfold ChainTerm.cancellationOutput
        rw [ite_eq_left (P.backtrack_right T)]
        rfl
      let U : Finset (Identification (P.append T).toShape T.reverse.toShape) := (univ.erase p₀).erase p₁
      have h₀ : p₀ ∈ (univ : Finset (Identification (P.append T).toShape T.reverse.toShape)) := mem_univ _
      have h₁ : p₁ ∈ univ.erase p₀ := mem_erase.mpr ⟨hNe,mem_univ _⟩
      have he : (∑ p, f p) - A - chainFamily C = ∑ p ∈ U, f p := by
        rw [← sum_erase_add _ _ h₀,← sum_erase_add _ _ h₁,hAppend,hBack]
        abel
      rw [he]
      apply Submodule.sum_mem
      intro p hp
      have h₁' := (mem_erase.mp hp).1
      have h₀' := (mem_erase.mp (mem_erase.mp hp).2).1
      exact single_output_mem C T T.reverse p h₀'
        (fun h ↦ h₁' (P.eq_backtrackIdentification T p h.1 h.2))
    · rw [ite_eq_right hS,sub_zero]
      have he : (∑ p, f p)-A = ∑ p ∈ univ.erase p₀, f p := by
        rw [← sum_erase_add _ _ (mem_univ p₀),hAppend]
        abel
      rw [he]
      apply Submodule.sum_mem
      intro p hp
      exact single_output_mem C T S p (mem_erase.mp hp).1
        (fun h ↦ hS (P.eq_reverse_of_backtrack T S p h.1 h.2))
  have h₁ : _ ∈ chainRemainders := (le_sup_right : errorSpace ≤ chainRemainders) hErr
  have h₂ : _ ∈ chainRemainders := (le_sup_left : pairSpace ≤ chainRemainders) hRemaining
  have h := Submodule.add_mem _ h₁ h₂
  convert h using 1
  abel

end LovaszTheta.Independent
