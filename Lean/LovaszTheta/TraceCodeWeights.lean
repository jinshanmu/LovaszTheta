module

public import LovaszTheta.TracePatterns

/-!
# Coefficient weights for one trace code

The code fixes the private pairs and their changes of coordinates.
Each of the two projections of an allowed shape pair is injective.
Cauchy–Schwarz therefore bounds the coefficient sum of a pair by one.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {J V : Type*} [Fintype J] {α : J → BasicShape} {l v : ℕ}

private lemma abs_coeff_le_one {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1) (j : J) :
    |c j| ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) zero_le_one
  rw [sq_abs,one_pow,← hc]
  exact single_le_sum (fun j _ ↦ sq_nonneg (c j)) (mem_univ _)

/-- The absolute coefficient weight of a contributing trace. -/
noncomputable def TraceWord.weight (c : J → ℝ) (w : TraceWord α V l) : ℝ :=
  ∏ i, |c (w.val i).1|

private abbrev ShapeChoices (α : J → BasicShape) (a : BoundaryChange) :=
  {p : J × J // InReturnFrame a (α p.1) (α p.2)}

private lemma sum_pair_weights_le_one (hα : Function.Injective α) {c : J → ℝ}
    (hc : ∑ j, (c j)^2 = 1) (a : BoundaryChange) :
    (∑ p : ShapeChoices α a, |c p.val.1| * |c p.val.2|) ≤ 1 := by
  have h₁ : Function.Injective (fun p : ShapeChoices α a ↦ p.val.1) := by
    intro p q he
    apply Subtype.ext
    change p.val.1 = q.val.1 at he
    exact Prod.ext he (hα (InReturnFrame.right_unique p.property (by rw [he]; exact q.property)))
  have h₂ : Function.Injective (fun p : ShapeChoices α a ↦ p.val.2) := by
    intro p q he
    apply Subtype.ext
    change p.val.2 = q.val.2 at he
    exact Prod.ext (hα (InReturnFrame.left_unique p.property (by rw [he]; exact q.property))) he
  have hPart (f : ShapeChoices α a → J) (hf : Function.Injective f) :
      (∑ p, |c (f p)|^2) ≤ 1 := by
    simp only [sq_abs]
    rw [← hc]
    calc
      _ = ∑ j ∈ (univ : Finset (ShapeChoices α a)).image f, (c j)^2 := (sum_image hf.injOn).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ ↦ sq_nonneg (c j))
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) zero_le_one
  rw [one_pow]
  exact (sum_mul_sq_le_sq_mul_sq univ (fun p : ShapeChoices α a ↦ |c p.val.1|)
    (fun p ↦ |c p.val.2|)).trans
    (by
      simpa only [mul_one] using
        mul_le_mul (hPart _ h₁) (hPart _ h₂) (sum_nonneg fun _ _ ↦ sq_nonneg _) zero_le_one)

private abbrev PrivatePairs (w : TraceWord α V l) :=
  {p : Fin (l+2) × Fin (l+2) // w.blocks.privatePair p.1 p.2}

private def pairEndpoint (w : TraceWord α V l) : PrivatePairs w ⊕ PrivatePairs w → Fin (l+2)
  | Sum.inl p => p.val.1
  | Sum.inr p => p.val.2

omit [Fintype J] in
private lemma pairEndpoint_injective (w : TraceWord α V l) : Function.Injective (pairEndpoint w) := by
  intro x y he
  rcases x with (x | x) <;> rcases y with (y | y)
  · change x.val.1 = y.val.1 at he
    have h := w.blocks.exactPair_right_unique x.property.1 (he.symm ▸ y.property.1)
    exact congrArg Sum.inl (Subtype.ext (Prod.ext he h))
  · change x.val.1 = y.val.2 at he
    exact (TraceBlocks.not_forward_and_return w.repeated
      (he ▸ (TraceBlocks.forward_return_of_exactPair w.repeated x.property.1).1)
      (TraceBlocks.forward_return_of_exactPair w.repeated y.property.1).2).elim
  · change x.val.2 = y.val.1 at he
    exact (TraceBlocks.not_forward_and_return w.repeated
      (TraceBlocks.forward_return_of_exactPair w.repeated y.property.1).1
      (he ▸ (TraceBlocks.forward_return_of_exactPair w.repeated x.property.1).2)).elim
  · change x.val.2 = y.val.2 at he
    have h := w.blocks.exactPair_left_unique x.property.1 (he.symm ▸ y.property.1)
    exact congrArg Sum.inr (Subtype.ext (Prod.ext h he))

/-- The weight of a collection of distinct patterns with a common code is at most one. -/
theorem sum_weights_le_one_of_code_eq {S : Type*} [Fintype S] (w : TraceWord α V l)
    (r : S → TraceWord α V l) (hα : Function.Injective α)
    (hv : ∀ j, (α j).additionalVertices ≤ v) {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1)
    (hDistinct : Function.Injective (fun s ↦ (r s).pattern v))
    (hCode : ∀ s i, TraceBlocks.encodeStep w.blocks v i = TraceBlocks.encodeStep (r s).blocks v i) :
    (∑ s, (r s).weight c) ≤ 1 := by
  let changeAt (p : PrivatePairs w) :=
    (w.blocks.block p.val.1).boundaryChange (w.blocks.block p.val.2)
  let choice (s : S) (p : PrivatePairs w) : ShapeChoices α (changeAt p) :=
    ⟨((r s).val p.val.1 |>.1,(r s).val p.val.2 |>.1),by
      have h := TraceBlocks.returnAgreement_of_code_eq w.repeated (r s).repeated (hCode s) p.property
      dsimp only [changeAt]
      rw [h.boundaryChange_eq]
      exact LabeledBlock.inReturnFrame_of_graph_eq _ _ h.paired.1.2.2.2.1
        (TraceBlocks.return_left_is_endpoint h.paired)⟩
  have hInj : Function.Injective choice := by
    intro s t he
    apply hDistinct
    apply TraceWord.pattern_eq_of_code_eq hα hv (fun i ↦ (hCode s i).symm.trans (hCode t i))
    intro i j h
    let p : PrivatePairs w := ⟨(i,j),
      (TraceBlocks.returnAgreement_of_code_eq (r s).repeated w.repeated
        (fun k ↦ (hCode s k).symm) h).paired⟩
    exact congrArg (fun q : ShapeChoices α (changeAt p) ↦ q.val.1) (congrFun he p)
  let a (p : PrivatePairs w) (q : ShapeChoices α (changeAt p)) := |c q.val.1| * |c q.val.2|
  have hPoint (s : S) : (r s).weight c ≤ ∏ p, a p (choice s p) := by
    let weightAt (i : Fin (l+2)) := |c ((r s).val i).1|
    have hSub := prod_le_prod_of_subset_of_le_one₀
      (f := weightAt) (subset_univ (univ.image (pairEndpoint w)))
      (fun _ _ ↦ abs_nonneg _) (fun _ _ _ ↦ abs_coeff_le_one hc _)
    unfold TraceWord.weight
    apply hSub.trans_eq
    rw [prod_image (pairEndpoint_injective w).injOn, Fintype.prod_sum_type,← prod_mul_distrib]
    rfl
  calc
    _ ≤ ∑ f : (p : PrivatePairs w) → ShapeChoices α (changeAt p), ∏ p, a p (f p) :=
      sum_le_sum_of_injOn choice hInj.injOn (subset_univ _) (fun s _ ↦ hPoint s)
        (fun f _ _ ↦ prod_nonneg fun p _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ∏ p, ∑ q, a p q := (Fintype.prod_sum a).symm
    _ ≤ ∏ _p : PrivatePairs w, (1 : ℝ) :=
      prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (fun p _ ↦ sum_pair_weights_le_one hα hc (changeAt p))
    _ = 1 := prod_const_one

end LovaszTheta.Independent
