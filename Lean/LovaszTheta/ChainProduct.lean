module

public import LovaszTheta.ChainAppend
public import LovaszTheta.CancellationOutputs
public import LovaszTheta.FallingFactorialLimit
public import LovaszTheta.NormErrors

/-!
# The chain product

The exact identification expansion leaves the append term and the
admissible exact cancellations. All other terms have strictly
negative power in the rough estimate. The falling factorial turns
each retained term into a coefficient of one, up to vanishing error.
-/

@[expose] public section

open Finset Filter SimpleGraph
open scoped Classical Topology Matrix.Norms.L2Operator

namespace LovaszTheta.Independent.ChainTerm

/-- The normalization power of a chain or pair. -/
noncomputable def normalizationPower (P : ChainTerm) : ℝ := -((P.span : ℝ)+P.extra)/2

/-- The normalization power shared by the identifications in the product. -/
noncomputable def productPower (P : ChainTerm) (S : BasicShape) : ℝ :=
  P.normalizationPower-(S.span : ℝ)/2

lemma reachable_boundary_of_extra_zero (P : ChainTerm) (h : P.extra = 0) :
    P.graph.Reachable P.toShape.left P.toShape.right := by
  apply P.right_reachable_of_single
  cases he : P.leftChain with
  | none => rfl
  | some C => simp [extra,he] at h

private lemma extra_le_one (P : ChainTerm) : P.extra ≤ 1 := by
  cases he : P.leftChain <;> simp [extra,he]

private lemma rough_le_of_normalized (P : ChainTerm) :
    P.normalizationPower+roughExponent P.toShape ≤ 0 := by
  have hIso : P.toShape.isolatedInterior = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hn := (mem_filter.mp ha).2
    obtain ⟨b,hb⟩ := P.incident_of_not_boundaries a hn.1 hn.2.1
    exact hn.2.2 b hb
  have hInd : P.toShape.boundaryIndicator ≤ P.span+1 := by
    unfold Shape.boundaryIndicator
    split_ifs <;> omega
  unfold roughExponent normalizationPower
  rw [hIso,card_empty,Nat.add_zero,Nat.cast_sub hInd]
  push_cast
  by_cases h : P.extra = 0
  · have he : P.toShape.boundaryIndicator = 1 := by
      unfold Shape.boundaryIndicator
      rw [ite_eq_left (P.reachable_boundary_of_extra_zero h)]
    rw [h,he]
    norm_num
    linarith
  · have h₁ : P.extra = 1 := by have hh := P.extra_le_one; omega
    rw [h₁]
    have h₀ : 0 ≤ (P.toShape.boundaryIndicator : ℝ) := Nat.cast_nonneg _
    linarith

private lemma product_net_power (P : ChainTerm) (S : BasicShape)
    (p : Identification P.toShape S.toShape) :
    P.productPower S + roughExponent p.shape =
      (2-(p.liveShared.card : ℝ)-p.shape.boundaryIndicator-P.extra)/2 := by
  have h := p.normalized_rough_exponent P.incident_of_not_boundaries S.incident P.extra
  change _ / 2 - (((P.span+1 : ℕ) : ℝ)+((S.span+1 : ℕ) : ℝ)-2+P.extra)/2 = _ at h
  unfold productPower normalizationPower roughExponent
  simp only [span,BasicShape.span,Nat.cast_add,Nat.cast_one] at h ⊢
  linarith

private lemma product_net_neg_of_two (P : ChainTerm) (S : BasicShape)
    (p : Identification P.toShape S.toShape) (hCard : 2 ≤ p.liveShared.card)
    (hConnect : p.liveShared.card ≤ 2 → P.graph.Reachable P.toShape.left P.toShape.right →
      p.remaining.Reachable p.outputLeft p.outputRight) :
    P.productPower S + roughExponent p.shape < 0 := by
  rw [product_net_power]
  have hCard' : (2 : ℝ) ≤ p.liveShared.card := by exact_mod_cast hCard
  have hE₀ : 0 ≤ (P.extra : ℝ) := Nat.cast_nonneg _
  have hI₀ : 0 ≤ (p.shape.boundaryIndicator : ℝ) := Nat.cast_nonneg _
  by_cases hgt : 2 < p.liveShared.card
  · have he : (2 : ℝ) < p.liveShared.card := by exact_mod_cast hgt
    linarith
  by_cases hE : P.extra = 0
  · have hPath := hConnect (Nat.le_of_not_gt hgt) (P.reachable_boundary_of_extra_zero hE)
    have hI : p.shape.boundaryIndicator = 1 := by
      unfold Shape.boundaryIndicator
      rw [ite_eq_left (p.reachable_iff.mpr hPath)]
    rw [hI]
    norm_num
    linarith
  · have he : (0 : ℝ) < P.extra := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hE)
    linarith

private lemma product_net_neg_no_cancels (P : ChainTerm) (S : BasicShape)
    (p : Identification P.toShape S.toShape) (hB : ¬∃ a, Incident p.newCancels a)
    (hf : p ≠ Identification.fresh P.toShape S.toShape) :
    P.productPower S + roughExponent p.shape < 0 := by
  have hDisj {a b : p.Vertex} (h : p.oldGraph.Adj a b) : ¬p.newGraph.Adj a b :=
    p.disjoint_of_no_newCancels hB h
  apply P.product_net_neg_of_two S p
  · rw [p.liveShared_eq_shared_of_disjoint hDisj S.incident]
    by_contra! h
    exact hf (p.eq_fresh_of_card_shared_le_one (by omega))
  · exact fun _ hP ↦ p.reachable_of_disjoint hDisj hP S.preconnected

private lemma exact_net_neg_no_output (P : ChainTerm) (T S : BasicShape)
    (p : Identification (P.append T).toShape S.toShape)
    (h : p.newGraph = P.lastGraph T S p) (hOut : P.cancellationOutput T S p = none) :
    (P.append T).productPower S + roughExponent p.shape < 0 := by
  have hW : p.outputRight ≠ P.junction T S p := by
    intro he
    simp [cancellationOutput,he] at hOut
  have hL : P.leftChain ≠ none := by
    intro he
    simp [cancellationOutput,hW,he] at hOut
  have hR : P.rightChain ≠ [] := by
    intro he
    simp [cancellationOutput,hW,hL,he] at hOut
  have hSet : p.liveShared = {p.outputRight,P.junction T S p} := by
    ext u
    rw [P.liveShared_iff_of_exact T S p h]
    have hKeep : P.keepsJunction := Or.inr hR
    simp only [mem_insert,mem_singleton,hKeep,and_true]
  have hE : (P.append T).extra = 1 := by
    cases he : P.leftChain with
    | none => exact (hL he).elim
    | some C => simp only [append,extra,he,Option.elim_some]
  rw [product_net_power,hSet,card_pair hW,hE]
  have hI : (0 : ℝ) ≤ p.shape.boundaryIndicator := Nat.cast_nonneg _
  norm_num
  linarith

private lemma exact_output_power (P : ChainTerm) (T S : BasicShape)
    (p : Identification (P.append T).toShape S.toShape)
    (h : p.newGraph = P.lastGraph T S p) {Q : ChainTerm} (hQ : P.cancellationOutput T S p = some Q) :
    (P.append T).productPower S + ((p.shape.vertexCount-Q.toShape.vertexCount : ℕ) : ℝ) =
      Q.normalizationPower := by
  have hSize := P.size_eq_of_exact T S p h
  have hCount := P.quotient_size_of_exact T S p h
  have hT := T.span_pos
  have hP (hQ : Q = P) : (P.append T).productPower S + ((p.shape.vertexCount-Q.toShape.vertexCount : ℕ) : ℝ) =
      Q.normalizationPower := by
    subst Q
    have hN : p.shape.vertexCount-P.toShape.vertexCount = T.span := by
      rw [hCount]
      change ((P.append T).span+1)-(P.span+1) = T.span
      rw [span_append]
      omega
    rw [hN,productPower,normalizationPower,normalizationPower,span_append,hSize]
    change -((((P.span+T.span : ℕ) : ℝ))+P.extra)/2-(T.span : ℝ)/2+T.span = -((P.span : ℝ)+P.extra)/2
    push_cast
    ring
  unfold cancellationOutput at hQ
  split_ifs at hQ with hW hL hR
  · exact hP (Option.some.inj hQ).symm
  · have he := Option.some.inj hQ
    subst Q
    have hp : P.span = Chain.span P.rightChain := by simp [hL,offset]
    have hV : (pair P.rightChain []).span = P.span+1 := by
      rw [hp]
      exact Nat.zero_add _
    have hN : p.shape.vertexCount-(pair P.rightChain []).toShape.vertexCount = T.span-1 := by
      rw [hCount]
      change ((P.append T).span+1)-((pair P.rightChain []).span+1) = T.span-1
      rw [hV,span_append]
      omega
    rw [hN,productPower,normalizationPower,normalizationPower,span_append,hSize,hV,
      Nat.cast_sub (Nat.succ_le_of_lt hT)]
    simp only [extra,append,hL,Option.elim_none,Option.elim_some,Nat.cast_add,Nat.cast_one]
    ring
  · exact hP (Option.some.inj hQ).symm

/-- The surviving identification in a product with an empty right component. -/
noncomputable def emptyProductOutput (P : ChainTerm) (S : BasicShape)
    (p : Identification P.toShape S.toShape) : Option ChainTerm :=
  if p = Identification.fresh P.toShape S.toShape then some (P.append S) else none

/-- The surviving term of a product with a nonempty right chain. -/
noncomputable def nonemptyProductOutput (P : ChainTerm) (T S : BasicShape)
    (p : Identification (P.append T).toShape S.toShape) : Option ChainTerm :=
  if p = Identification.fresh (P.append T).toShape S.toShape then some ((P.append T).append S)
  else if p.newGraph = P.lastGraph T S p then P.cancellationOutput T S p else none

/-- Interpret a surviving term as a normalized matrix, and an omitted term as zero. -/
noncomputable def outputMatrix (o : Option ChainTerm) (n : ℕ) (x : SignSample n) :
    Matrix (Fin n) (Fin n) ℝ := o.elim 0 (fun Q ↦ Q.matrix x)

private lemma term_vanishes_of_neg (P : ChainTerm) (S : BasicShape)
    (p : Identification P.toShape S.toShape) (h : P.productPower S+roughExponent p.shape < 0) :
    NormVanishes (fun n x ↦ (n : ℝ)^(P.productPower S) • graphMatrix p.shape x) :=
  normVanishes_smul_graphMatrix _ _ zero_le_one h
    (Eventually.of_forall fun n ↦ by rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),one_mul])

private lemma fresh_normalized (P : ChainTerm) (S : BasicShape) {n : ℕ} (x : SignSample n) :
    (n : ℝ)^(P.productPower S) • graphMatrix (Identification.fresh P.toShape S.toShape).shape x =
      (P.append S).matrix x := by
  obtain ⟨e⟩ := P.fresh_isomorphic_append S
  rw [e.graphMatrix_eq]
  have he : P.productPower S = (P.append S).normalizationPower := by
    rw [productPower,normalizationPower,normalizationPower,span_append]
    change -((P.span : ℝ)+P.extra)/2-(S.span : ℝ)/2 =
      -((((P.span+S.span : ℕ) : ℝ))+P.extra)/2
    push_cast
    ring
  rw [he]
  rfl

private lemma exact_term_vanishes_diff (P : ChainTerm) (T S : BasicShape)
    (p : Identification (P.append T).toShape S.toShape)
    (h : p.newGraph = P.lastGraph T S p) {Q : ChainTerm} (hQ : P.cancellationOutput T S p = some Q) :
    NormVanishes (fun n x ↦ (n : ℝ)^((P.append T).productPower S) • graphMatrix p.shape x - Q.matrix x) := by
  let r := (P.append T).productPower S
  let q := Q.toShape.vertexCount
  let z := p.shape.vertexCount-q
  have hPower : r+(z : ℝ) = Q.normalizationPower := P.exact_output_power T S p h hQ
  have hr : r+(z : ℝ)-1+roughExponent Q.toShape < 0 := by
    have he := Q.rough_le_of_normalized
    linarith
  let a (n : ℕ) := (n : ℝ)^r * (((n-q).descFactorial z : ℝ)-(n : ℝ)^z)
  have hA : ∀ᶠ n : ℕ in atTop, |a n| ≤ ((z : ℝ)*(q+z))*(n : ℝ)^(r+(z : ℝ)-1) := by
    filter_upwards [eventually_ge_atTop (max 1 (q+z))] with n hn
    have hn₁ : 0 < n := by omega
    have hS : q+z ≤ n := (le_max_right _ _).trans hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn₁
    unfold a
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hnR.le _)]
    refine (mul_le_mul_of_nonneg_left (abs_descFactorial_sub_pow_le hn₁ hS) (Real.rpow_nonneg hnR.le _)).trans_eq ?_
    rw [show r+(z : ℝ)-1 = r+((z : ℝ)-1) by ring,Real.rpow_add hnR]
    ring
  refine (normVanishes_smul_graphMatrix Q.toShape a (by positivity) hr hA).congr ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn x
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold a
  rw [P.graphMatrix_eq_output T S p h hQ]
  change _ • graphMatrix Q.toShape x =
    (n : ℝ)^r • (((n-q).descFactorial z : ℝ) • graphMatrix Q.toShape x) -
      (n : ℝ)^(Q.normalizationPower) • graphMatrix Q.toShape x
  rw [smul_smul,← hPower,Real.rpow_add hnR,Real.rpow_natCast,← sub_smul,mul_sub]

/-- The normalized matrix of the basic multiplying block. -/
noncomputable def blockMatrix (S : BasicShape) {n : ℕ} (x : SignSample n) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)^(-(S.span : ℝ)/2) • graphMatrix S.toShape x

private lemma matrix_mul_blockMatrix_eq (P : ChainTerm) (S : BasicShape) {n : ℕ}
    (hn : 0 < n) (x : SignSample n) :
    P.matrix x * blockMatrix S x =
      ∑ p : Identification P.toShape S.toShape, (n : ℝ)^(P.productPower S) • graphMatrix p.shape x := by
  have he : (n : ℝ)^(P.productPower S) =
      (n : ℝ)^(P.normalizationPower)*(n : ℝ)^(-(S.span : ℝ)/2) := by
    rw [productPower,sub_eq_add_neg,Real.rpow_add (Nat.cast_pos.mpr hn),neg_div]
  change ((n : ℝ)^(P.normalizationPower) • graphMatrix P.toShape x) *
      ((n : ℝ)^(-(S.span : ℝ)/2) • graphMatrix S.toShape x) = _
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,← he,Identification.graphMatrix_mul_eq_sum,smul_sum]

private lemma normVanishes_product_of_terms (P : ChainTerm) (S : BasicShape)
    (out : Identification P.toShape S.toShape → Option ChainTerm)
    (h : ∀ p, NormVanishes (fun n x ↦ (n : ℝ)^(P.productPower S) • graphMatrix p.shape x -
      outputMatrix (out p) n x)) :
    NormVanishes (fun n x ↦ P.matrix x * blockMatrix S x - ∑ p, outputMatrix (out p) n x) := by
  refine (NormVanishes.sum univ _ (fun p _ ↦ h p)).congr ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn x
  rw [sum_sub_distrib,P.matrix_mul_blockMatrix_eq S (by omega) x]

/-- Multiplication appends a block when the right component is empty. -/
theorem normVanishes_empty_product (P : ChainTerm) (S : BasicShape) (hP : P.rightChain = []) :
    NormVanishes (fun n x ↦ P.matrix x * blockMatrix S x -
      ∑ p, outputMatrix (P.emptyProductOutput S p) n x) := by
  apply normVanishes_product_of_terms
  intro p
  by_cases hf : p = Identification.fresh P.toShape S.toShape
  · subst p
    apply NormVanishes.of_zero.congr
    apply Eventually.of_forall
    intro n x
    simp [emptyProductOutput,outputMatrix,fresh_normalized]
  · have hPow : P.productPower S+roughExponent p.shape < 0 := by
      by_cases hB : ∃ a, Incident p.newCancels a
      · have hR : ∃ a, Incident p.newSurvives a := by
          by_contra h
          exact P.not_le_old_of_empty hP p (p.newGraph_le_oldGraph_of_no_survivors h)
        obtain ⟨hc,hh⟩ := p.partial_new_cancellation S.vertexDeletionConnected
          (S.incident S.toShape.right) hR hB
        exact P.product_net_neg_of_two S p hc hh
      · exact P.product_net_neg_no_cancels S p hB hf
    refine (P.term_vanishes_of_neg S p hPow).congr (Eventually.of_forall fun n x ↦ ?_)
    simp only [emptyProductOutput,ite_eq_right hf,outputMatrix,Option.elim_none,sub_zero]

/-- Multiplication of a nonempty chain term has the append term and exactly the
admissible last-block cancellations, all with coefficients one up to the stated error. -/
theorem normVanishes_nonempty_product (P : ChainTerm) (T S : BasicShape) :
    NormVanishes (fun n x ↦ (P.append T).matrix x * blockMatrix S x -
      ∑ p, outputMatrix (P.nonemptyProductOutput T S p) n x) := by
  apply normVanishes_product_of_terms
  intro p
  by_cases hf : p = Identification.fresh (P.append T).toShape S.toShape
  · subst p
    apply NormVanishes.of_zero.congr
    apply Eventually.of_forall
    intro n x
    simp [nonemptyProductOutput,outputMatrix,fresh_normalized]
  by_cases he : p.newGraph = P.lastGraph T S p
  · cases hO : P.cancellationOutput T S p with
    | none =>
      refine ((P.append T).term_vanishes_of_neg S p (P.exact_net_neg_no_output T S p he hO)).congr ?_
      exact Eventually.of_forall fun n x ↦ by
        simp only [nonemptyProductOutput,ite_eq_right hf,ite_eq_left he,hO,outputMatrix,Option.elim_none,sub_zero]
    | some Q =>
      exact (P.exact_term_vanishes_diff T S p he hO).congr (Eventually.of_forall fun n x ↦ by
        simp only [nonemptyProductOutput,ite_eq_right hf,ite_eq_left he,hO,outputMatrix,Option.elim_some])
  · have hPow : (P.append T).productPower S+roughExponent p.shape < 0 := by
      by_cases hB : ∃ a, Incident p.newCancels a
      · by_cases hR : ∃ a, Incident p.newSurvives a
        · obtain ⟨hc,hh⟩ := p.partial_new_cancellation S.vertexDeletionConnected
            (S.incident S.toShape.right) hR hB
          exact (P.append T).product_net_neg_of_two S p hc hh
        · have hLast := P.newGraph_le_last_of_le_old T S p (p.newGraph_le_oldGraph_of_no_survivors hR)
          obtain ⟨hc,hh⟩ := P.partial_last_cancellation T S p hLast he
          exact (P.append T).product_net_neg_of_two S p hc hh
      · exact (P.append T).product_net_neg_no_cancels S p hB hf
    refine ((P.append T).term_vanishes_of_neg S p hPow).congr (Eventually.of_forall fun n x ↦ ?_)
    simp only [nonemptyProductOutput,ite_eq_right hf,ite_eq_right he,outputMatrix,Option.elim_none,sub_zero]

end LovaszTheta.Independent.ChainTerm
