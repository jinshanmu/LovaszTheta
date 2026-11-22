module

public import LovaszTheta.TraceCodeCount

/-!
# The sharp trace moment

The label factor is (n^{1-t/2}) at defect (t).
The coefficient sum at that defect is bounded by the number of codes.
This gives a geometric series after collecting the defect classes.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Independent

variable {J : Type*} [Fintype J] {α : J → BasicShape} {l v n : ℕ}

/-- A linear combination of the normalized basic graph matrices. -/
noncomputable def normalizedCombination (α : J → BasicShape) (c : J → ℝ)
    (x : EdgeIndex (Fin n) → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  basicCombination α (fun j ↦ c j * chainNormalization n (α j).toShape.vertexCount) x

private lemma sum_weights_le_code_count {S : Type*} [Fintype S] (r : S → TraceWord α (Fin n) l)
    {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1) (hα : Function.Injective α)
    (hv : ∀ j, (α j).additionalVertices ≤ v)
    (hDistinct : Function.Injective (fun s ↦ (r s).pattern v)) :
    (∑ s, (r s).weight c) ≤ ((univ.image fun s ↦ (r s).code v).card : ℝ) := by
  let code (s : S) := (r s).code v
  let codes := univ.image code
  rw [← sum_fiberwise_of_maps_to (g := code) (t := codes)
    (fun s _ ↦ mem_image_of_mem code (mem_univ s))]
  have hCard : (codes.card : ℝ) = ∑ _a ∈ codes, (1 : ℝ) := by rw [sum_const,nsmul_eq_mul,mul_one]
  change _ ≤ (codes.card : ℝ)
  rw [hCard]
  apply sum_le_sum
  intro a ha
  obtain ⟨s,_,hs⟩ := mem_image.mp ha
  let F := (univ : Finset S).filter (fun t ↦ code t = a)
  change (∑ t ∈ F, (r t).weight c) ≤ 1
  rw [← sum_coe_sort F]
  exact sum_weights_le_one_of_code_eq (r s) (fun t : F ↦ r t.val) hα hv hc
    (hDistinct.comp Subtype.val_injective)
    (fun t i ↦ congrFun (hs.trans (mem_filter.mp t.property).2.symm) i)

omit [Fintype J] in
private lemma group_normalization (hn : 0 < n) (w : TraceWord α (Fin n) l) :
    (n : ℝ)^w.labels.card * (∏ i, chainNormalization n (α (w.val i).1).toShape.vertexCount) =
      (n : ℝ) * ((n : ℝ)^(-(1/2 : ℝ)))^w.blocks.defect := by
  have hb : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hCount := congrArg (fun z : ℕ ↦ (z : ℝ)) (TraceBlocks.card_usedLabels_defect w.repeated)
  push_cast at hCount
  have hCount' : 2*(w.labels.card : ℝ)+(l+2)+(w.blocks.defect : ℝ) =
      2+∑ i, ((α (w.val i).1).toShape.vertexCount : ℝ) := by
    simpa only [TraceWord.labels, w.shape, BasicShape.toShape, Nat.cast_add, Nat.cast_ofNat] using hCount
  simp only [chainNormalization]
  have hRight : (n : ℝ) * ((n : ℝ)^(-(1/2 : ℝ)))^w.blocks.defect =
      (n : ℝ)^(1+(-(1/2 : ℝ))*(w.blocks.defect : ℝ)) := by
    rw [Real.rpow_add hb,Real.rpow_one,Real.rpow_mul hb.le,Real.rpow_natCast]
  rw [← Real.rpow_sum_of_pos hb,← Real.rpow_natCast (n : ℝ) w.labels.card,← Real.rpow_add hb,hRight]
  congr 1
  have he (i : Fin (l+2)) : -(((α (w.val i).1).toShape.vertexCount : ℝ)-1)/2 =
      ((1 : ℝ) - ((α (w.val i).1).toShape.vertexCount : ℝ))/2 := by ring
  simp_rw [he,← sum_div,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_add,
    Nat.cast_ofNat,mul_one]
  linarith

omit [Fintype J] in
private lemma weight_nonneg (c : J → ℝ) (w : TraceWord α (Fin n) l) : 0 ≤ w.weight c :=
  prod_nonneg fun _ _ ↦ abs_nonneg _

private lemma sum_labeled_weights_le (hv : ∀ j, (α j).additionalVertices ≤ v) (hn : 0 < n)
    (c : J → ℝ) (w : TraceWord α (Fin n) l) :
    (∑ z ∈ univ.filter (fun z : TraceWord α (Fin n) l ↦ z.pattern v = w.pattern v),
      ∏ i, c (z.val i).1 * chainNormalization n (α (z.val i).1).toShape.vertexCount) ≤
    (n : ℝ) * ((n : ℝ)^(-(1/2 : ℝ)))^w.blocks.defect * w.weight c := by
  let F := univ.filter (fun z : TraceWord α (Fin n) l ↦ z.pattern v = w.pattern v)
  let a := ∏ i, chainNormalization n (α (w.val i).1).toShape.vertexCount
  have ha : 0 ≤ a := prod_nonneg fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hCard : (F.card : ℝ) ≤ (n : ℝ)^w.labels.card := by
    exact_mod_cast (w.card_fiber_pattern_le hv).trans_eq (by rw [Fintype.card_fin])
  calc
    _ ≤ ∑ z ∈ F, w.weight c*a := by
      apply sum_le_sum
      intro z hz
      have hi i := TraceWord.shapeWord_eq (mem_filter.mp hz).2 i
      simp_rw [hi,prod_mul_distrib]
      apply mul_le_mul_of_nonneg_right _ ha
      rw [TraceWord.weight,← abs_prod]
      exact le_abs_self _
    _ = (F.card : ℝ)*a*w.weight c := by
      rw [sum_const,nsmul_eq_mul]
      ring
    _ ≤ (n : ℝ)^w.labels.card*a*w.weight c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCard ha) (weight_nonneg c w)
    _ = _ := by rw [group_normalization hn w]

private lemma geom_sum_le_inverse {q : ℝ} (h₀ : 0 ≤ q) (h₁ : q < 1) (r : ℕ) :
    (∑ t ∈ range r, q^t) ≤ 1/(1-q) := by
  apply (le_div_iff₀ (sub_pos.mpr h₁)).mpr
  have he := geom_sum_mul q r
  have hp := pow_nonneg h₀ r
  linarith only [he,hp]

/-- The finite trace moment with the geometric defect correction. -/
theorem average_trace_normalizedCombination_le_geom (hn : 0 < n)
    (hα : Function.Injective α) (hv : ∀ j, (α j).additionalVertices ≤ v)
    {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1)
    (hq : (traceCodeBase l v : ℝ)^traceCodeExponent v (Fintype.card J) *
      (n : ℝ)^(-(1/2 : ℝ)) ≤ 1/2) :
    average (fun x ↦ (normalizedCombination α c (n := n) x ^ (l+2)).trace) ≤
      (n : ℝ)*2^(l+2)/(1-((traceCodeBase l v : ℝ)^traceCodeExponent v (Fintype.card J) *
        (n : ℝ)^(-(1/2 : ℝ)))) := by
  let q := (traceCodeBase l v : ℝ)^traceCodeExponent v (Fintype.card J) * (n : ℝ)^(-(1/2 : ℝ))
  let W := TraceWord α (Fin n) l
  let P := (univ : Finset W).image (fun w ↦ w.pattern v)
  have hRepr (p : P) : ∃ w : W, w.pattern v = p.val := by
    obtain ⟨w,_,hw⟩ := mem_image.mp p.property
    exact ⟨w,hw⟩
  let r (p : P) := (hRepr p).choose
  have hr (p : P) : (r p).pattern v = p.val := (hRepr p).choose_spec
  let d (p : P) := (r p).blocks.defect
  let T := ((univ : Finset P).sup d)+1
  let b (p : P) : ℝ := (n : ℝ)*((n : ℝ)^(-(1/2 : ℝ)))^(d p)*(r p).weight c
  have hExpansion : (average fun x ↦ (normalizedCombination α c (n := n) x ^ (l+2)).trace) =
      ∑ f : Fin (l+2) → BasicLabeling α (Fin n), if stitched f ∧ evenEdgeMultiplicity f then
        ∏ i, c (f i).1 * chainNormalization n (α (f i).1).toShape.vertexCount else 0 :=
    by
      have h := average_trace_basicCombination_pow (V := Fin n) (α := α)
        (fun j ↦ c j * chainNormalization n (α j).toShape.vertexCount) (l+1)
      have hDec : (fun a b : Fin n ↦ Classical.propDecidable (a = b)) = instDecidableEqFin n :=
        Subsingleton.elim _ _
      rw [hDec] at h
      exact h
  rw [hExpansion]
  rw [← sum_filter]
  have hA : (∑ f : Fin (l+2) → BasicLabeling α (Fin n) with stitched f ∧ evenEdgeMultiplicity f,
      ∏ i, c (f i).1 * chainNormalization n (α (f i).1).toShape.vertexCount) =
      ∑ w : W, ∏ i, c (w.val i).1 * chainNormalization n (α (w.val i).1).toShape.vertexCount :=
    sum_subtype _ (fun _ ↦ by simp) _
  rw [hA,← sum_fiberwise_of_maps_to (t := P) (fun w _ ↦ mem_image_of_mem _ (mem_univ w))]
  have hFirst :
      (∑ p ∈ P, ∑ w : W with w.pattern v = p,
        ∏ i, c (w.val i).1 * chainNormalization n (α (w.val i).1).toShape.vertexCount) ≤
        ∑ p : P, b p := by
    rw [← sum_coe_sort P]
    apply sum_le_sum
    intro p _
    rw [← hr p]
    exact sum_labeled_weights_le hv hn c (r p)
  refine hFirst.trans ?_
  rw [← sum_fiberwise_of_maps_to (g := d) (t := range T)
    (fun p hp ↦ mem_range.mpr (Nat.lt_succ_of_le (le_sup hp)))]
  have hPer (t : ℕ) : (∑ p : P with d p = t, b p) ≤ (n : ℝ)*2^(l+2)*q^t := by
    let F := (univ : Finset P).filter (fun p ↦ d p = t)
    have hD (p : F) : d p.val = t := (mem_filter.mp p.property).2
    let r' (p : F) : W := r p.val
    have hInj : Function.Injective (fun p ↦ (r' p).pattern v) := by
      intro p z he
      change (r p.val).pattern v = (r z.val).pattern v at he
      rw [hr,hr] at he
      exact Subtype.ext (Subtype.ext he)
    have hWeight : (∑ p : F, (r' p).weight c) ≤
        (2 : ℝ)^(l+2)*(traceCodeBase l v : ℝ)^(traceCodeExponent v (Fintype.card J)*t) :=
      (sum_weights_le_code_count r' hc hα hv hInj).trans (by exact_mod_cast card_codes_le r' t hv hD)
    change (∑ p ∈ F, b p) ≤ _
    rw [← sum_coe_sort F]
    have hTerm (p : F) : b p.val = ((n : ℝ)*((n : ℝ)^(-(1/2 : ℝ)))^t)*(r' p).weight c := by
      unfold b
      rw [hD p]
    simp_rw [hTerm,← mul_sum]
    have hFactor : 0 ≤ (n : ℝ)*((n : ℝ)^(-(1/2 : ℝ)))^t :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
    refine (mul_le_mul_of_nonneg_left hWeight hFactor).trans_eq ?_
    unfold q
    rw [mul_pow, pow_mul]
    ring
  calc
    _ ≤ ∑ t ∈ range T, (n : ℝ)*2^(l+2)*q^t := sum_le_sum fun t _ ↦ hPer t
    _ = (n : ℝ)*2^(l+2)*(∑ t ∈ range T, q^t) := by rw [mul_sum]
    _ ≤ _ := by
      have hq₀ : 0 ≤ q := by dsimp [q]; positivity
      have hq₁ : q < 1 := lt_of_le_of_lt hq (by norm_num)
      exact (mul_le_mul_of_nonneg_left (geom_sum_le_inverse hq₀ hq₁ T)
        (by positivity : (0 : ℝ) ≤ (n : ℝ)*2^(l+2))).trans_eq (by ring)

/-- The trace moment is at most (2n2^{l+2}) once the defect ratio is at most one half. -/
theorem average_trace_normalizedCombination_le (hn : 0 < n)
    (hα : Function.Injective α) (hv : ∀ j, (α j).additionalVertices ≤ v)
    {c : J → ℝ} (hc : ∑ j, (c j)^2 = 1)
    (hq : (traceCodeBase l v : ℝ)^traceCodeExponent v (Fintype.card J) *
      (n : ℝ)^(-(1/2 : ℝ)) ≤ 1/2) :
    average (fun x ↦ (normalizedCombination α c (n := n) x ^ (l+2)).trace) ≤
      2*(n : ℝ)*2^(l+2) := by
  refine (average_trace_normalizedCombination_le_geom hn hα hv hc hq).trans ?_
  apply (div_le_iff₀ (by linarith)).mpr
  have hQ : (1 : ℝ) ≤ 2*(1-(traceCodeBase l v : ℝ)^traceCodeExponent v (Fintype.card J) *
      (n : ℝ)^(-(1/2 : ℝ))) := by linarith
  have h := mul_le_mul_of_nonneg_left hQ
    (by positivity : (0 : ℝ) ≤ (n : ℝ)*2^(l+2))
  linarith only [h]

end LovaszTheta.Independent
