module

public import LovaszTheta.TreeFields
public import LovaszTheta.ExchangeableSigns

/-!
# Second moments of the tree coordinates

A fixed sign support restricts each leaf label to the residues in that
support. Walsh orthogonality and the normalization then bound the
second moment uniformly in the modulus and frequency.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

variable {n : ℕ} [NeZero n]

private noncomputable def assignmentCount (T : RootedTree) (I : Finset (InversionClass n)) :
    ℕ :=
  (univ.filter fun a : T.Assignment n ↦ T.signSupport a = I).card

private lemma assignmentCount_sum (T : RootedTree) :
    (∑ I : Finset (InversionClass n), assignmentCount T I) = Fintype.card (T.Assignment n) := by
  unfold assignmentCount
  simp only [card_filter]
  rw [Finset.sum_comm]
  simp

private lemma assignmentCount_le (T : RootedTree) (I : Finset (InversionClass n)) :
    assignmentCount T I ≤ (2 * T.nodeCount) ^ Fintype.card T.Leaf := by
  let F := (univ : Finset (T.Assignment n)).filter fun a ↦ T.signSupport a = I
  let labels := I.biUnion fun c ↦ c.val
  by_cases hF : F.Nonempty
  · obtain ⟨a, ha⟩ := hF
    have haEq := (mem_filter.mp ha).2
    have hI : I.card = T.nodeCount := haEq ▸ T.signSupport_card a
    have hLabels : labels.card ≤ 2 * T.nodeCount := by
      calc
        _ ≤ ∑ c ∈ I, c.val.card := Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ I, 2 := sum_le_sum fun c _ ↦ inversionClass_card_le c
        _ = _ := by simp [hI, mul_comm]
    have in_labels (a : F) (u : T.Leaf) : a.val.val u ∈ labels := by
      let c := T.classEmbedding a.val u.val
      have hc : c ∈ T.signSupport a.val := mem_map.mpr ⟨u.val, mem_univ _, rfl⟩
      rw [(mem_filter.mp a.property).2] at hc
      apply mem_biUnion.mpr
      refine ⟨c, hc, ?_⟩
      change a.val.val u ∈ {T.residue a.val.val u.val, -T.residue a.val.val u.val}
      rw [residue_leaf]
      exact mem_insert_self _ _
    let encode (a : F) (u : T.Leaf) : labels := ⟨a.val.val u, in_labels a u⟩
    have hEncode : Function.Injective encode := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      funext u
      exact congrArg Subtype.val (congrFun he u)
    calc
      assignmentCount T I = Fintype.card F := (Fintype.card_coe F).symm
      _ ≤ Fintype.card (T.Leaf → labels) := Fintype.card_le_of_injective encode hEncode
      _ = labels.card ^ Fintype.card T.Leaf := by rw [Fintype.card_fun, Fintype.card_coe]
      _ ≤ _ := Nat.pow_le_pow_left hLabels _
  · change F.card ≤ _
    simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty, zero_le]

/-- A specified support bounds the number of possible leaf assignments. -/
lemma card_assignment_support_le (T : RootedTree) (I : Finset (InversionClass n)) :
    (univ.filter (fun a : T.Assignment n ↦ T.signSupport a = I)).card ≤
      (2 * T.nodeCount) ^ Fintype.card T.Leaf :=
  assignmentCount_le T I

private lemma abs_fieldCoefficient_le (T : RootedTree) (k : ZMod n) (I : Finset (InversionClass n)) :
    |T.fieldCoefficient k I| ≤ T.fieldNormalizer n * assignmentCount T I := by
  have hNorm : 0 ≤ T.fieldNormalizer n := by unfold fieldNormalizer; positivity
  unfold fieldCoefficient
  rw [abs_mul, abs_of_nonneg hNorm]
  apply mul_le_mul_of_nonneg_left _ hNorm
  calc
    _ ≤ ∑ a : T.Assignment n,
        |if T.signSupport a = I then (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : T.Assignment n, if T.signSupport a = I then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      split_ifs
      · exact (Complex.abs_re_le_norm _).trans_eq (by rw [ZMod.stdAddChar_apply, Circle.norm_coe])
      · norm_num
    _ = _ := by
      unfold assignmentCount
      rw [card_filter]
      push_cast
      exact sum_congr rfl fun _ _ ↦ by split_ifs <;> norm_num

/-- The squared standardization cancels the number of leaf assignments. -/
lemma fieldNormalizer_sq_mul (T : RootedTree) :
    T.fieldNormalizer n ^ 2 * (n : ℝ) ^ Fintype.card T.Leaf ≤ 1 := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnp : 0 < (n : ℝ) ^ Fintype.card T.Leaf := pow_pos hn _
  have hAut : 1 ≤ (Fintype.card T.Automorphism : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := T.Automorphism)
  have hAutoPos : 0 < (Fintype.card T.Automorphism : ℝ) := zero_lt_one.trans_le hAut
  unfold fieldNormalizer
  rw [inv_pow, mul_pow, Real.sq_sqrt hnp.le, Real.sq_sqrt hAutoPos.le, mul_inv,
    mul_comm (((n : ℝ) ^ Fintype.card T.Leaf)⁻¹), mul_assoc, inv_mul_cancel₀ hnp.ne', mul_one]
  exact inv_le_one_of_one_le₀ hAut

/-- The variance of a tree coordinate is bounded uniformly in frequency and modulus. -/
theorem average_field_sq_le (T : RootedTree) (k : ZMod n) :
    average (fun x ↦ T.field x k ^ 2) ≤ ((2 * T.nodeCount : ℕ) : ℝ) ^ Fintype.card T.Leaf := by
  let C : ℝ := ((2 * T.nodeCount : ℕ) : ℝ) ^ Fintype.card T.Leaf
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hMax (I : Finset (InversionClass n)) : (assignmentCount T I : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast assignmentCount_le T I
  have hCount : (Fintype.card (T.Assignment n) : ℝ) ≤ (n : ℝ) ^ Fintype.card T.Leaf := by
    have hInj := Fintype.card_le_of_injective (fun a : T.Assignment n ↦ a.val) Subtype.val_injective
    rw [Fintype.card_fun, ZMod.card] at hInj
    exact_mod_cast hInj
  have hExpand (x : InversionClass n → Bool) :
      T.field x k = walshCombination (T.fieldCoefficient k) x := T.field_walsh_expansion x k
  simp_rw [hExpand, pow_two, average_walshCombination_mul]
  have hI (I : Finset (InversionClass n)) :
      T.fieldCoefficient k I * T.fieldCoefficient k I ≤
        (T.fieldNormalizer n ^ 2 * C) * assignmentCount T I := by
    have hAbs := abs_fieldCoefficient_le T k I
    have hN : 0 ≤ T.fieldNormalizer n := by unfold fieldNormalizer; positivity
    have hSq : T.fieldCoefficient k I ^ 2 ≤
        (T.fieldNormalizer n * assignmentCount T I) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hN (by positivity))]
      exact hAbs
    rw [mul_pow, pow_two (T.fieldCoefficient k I), pow_two (assignmentCount T I : ℝ)] at hSq
    refine hSq.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hMax I) (by positivity)) (sq_nonneg _)
  change _ ≤ C
  calc
    _ ≤ ∑ I, (T.fieldNormalizer n ^ 2 * C) * assignmentCount T I :=
      sum_le_sum fun I _ ↦ hI I
    _ = (T.fieldNormalizer n ^ 2 * C) * Fintype.card (T.Assignment n) := by
      rw [← mul_sum, ← Nat.cast_sum, assignmentCount_sum]
    _ ≤ (T.fieldNormalizer n ^ 2 * C) * (n : ℝ) ^ Fintype.card T.Leaf :=
      mul_le_mul_of_nonneg_left hCount (mul_nonneg (sq_nonneg _) hC)
    _ = C * (T.fieldNormalizer n ^ 2 * (n : ℝ) ^ Fintype.card T.Leaf) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (fieldNormalizer_sq_mul T) hC
    _ = C := mul_one _

private lemma fixedResidueCount_le (T : RootedTree) (v : T.Node) (r : ZMod n) :
    (univ.filter fun a : T.Assignment n ↦ T.residue a.val v = r).card ≤
      n ^ (Fintype.card T.Leaf - 1) := by
  let A := univ.filter fun a : T.Assignment n ↦ T.residue a.val v = r
  by_cases hA : A.Nonempty
  · obtain ⟨a, _⟩ := hA
    have hL : (T.descendantLeaves v).Nonempty := by
      by_contra h
      apply a.property.choose v
      simp [residue, Finset.not_nonempty_iff_eq_empty.mp h]
    let : DecidableEq T.Leaf := fun i j ↦ Classical.propDecidable (i = j)
    let B := {z : T.Leaf → ZMod n // ∀ _ : Unit, ∑ u ∈ T.descendantLeaves v, z u = r}
    let encode (z : A) : B := ⟨z.val.val, fun _ ↦ (mem_filter.mp z.property).2⟩
    have hEncode : Function.Injective encode := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : B ↦ z.val) h
    change A.card ≤ _
    rw [← Fintype.card_coe A]
    exact (Fintype.card_le_of_injective encode hEncode).trans (by
      simpa only [Fintype.card_unit] using
        card_leaf_sum_fibre_le (fun _ : Unit ↦ T.descendantLeaves v) (fun _ ↦ hL)
          (fun _ _ h ↦ (h (Subsingleton.elim _ _)).elim) (fun _ ↦ r))
  · change A.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hA, Finset.card_empty]
    exact Nat.zero_le _

private lemma assignmentCount_containing_le (T : RootedTree) (b : InversionClass n) :
    (∑ I : Finset (InversionClass n), if b ∈ I then assignmentCount T I else 0) ≤
      (2 * T.nodeCount) * n ^ (Fintype.card T.Leaf - 1) := by
  let R := univ.filter fun a : T.Assignment n ↦ b ∈ T.signSupport a
  let S (v : T.Node) := univ.filter fun a : T.Assignment n ↦ T.residue a.val v ∈ b.val
  have hCount : (∑ I : Finset (InversionClass n), if b ∈ I then assignmentCount T I else 0) =
      R.card := by
    unfold assignmentCount
    rw [show R.card = ∑ a : T.Assignment n, if b ∈ T.signSupport a then 1 else 0 from
      card_filter _ _]
    have hTerm (I : Finset (InversionClass n)) :
        (if b ∈ I then (univ.filter fun a : T.Assignment n ↦ T.signSupport a = I).card else 0) =
          ∑ a : T.Assignment n, if T.signSupport a = I ∧ b ∈ I then 1 else 0 := by
      by_cases hi : b ∈ I
      · simp only [hi, ite_true, and_true, card_filter]
      · simp [hi]
    simp_rw [hTerm]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro a _
    have hMatch (I : Finset (InversionClass n)) :
        (if T.signSupport a = I ∧ b ∈ I then (1 : ℕ) else 0) =
          if T.signSupport a = I then if b ∈ T.signSupport a then 1 else 0 else 0 := by
      by_cases h : T.signSupport a = I <;> simp [h]
    simp_rw [hMatch, sum_ite_eq, mem_univ, ite_true]
  have hSubset : R ⊆ univ.biUnion S := by
    intro a ha
    have hm : b ∈ T.signSupport a := (mem_filter.mp ha).2
    obtain ⟨v, _, hv⟩ := mem_map.mp hm
    refine mem_biUnion.mpr ⟨v, mem_univ v, mem_filter.mpr ⟨mem_univ a, ?_⟩⟩
    rw [← hv]
    exact Finset.mem_insert_self _ _
  have hSite (v : T.Node) : (S v).card ≤ 2 * n ^ (Fintype.card T.Leaf - 1) := by
    let f (r : ZMod n) := univ.filter fun a : T.Assignment n ↦ T.residue a.val v = r
    have hEq : S v = b.val.biUnion f := by
      ext a
      simp only [S, f, mem_filter, mem_biUnion, mem_univ, true_and]
      exact ⟨fun ha ↦ ⟨T.residue a.val v, ha, rfl⟩, fun ⟨_, hr, h⟩ ↦ h ▸ hr⟩
    calc
      _ ≤ ∑ r ∈ b.val, (f r).card := hEq ▸ Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ b.val, n ^ (Fintype.card T.Leaf - 1) := sum_le_sum fun r _ ↦
        fixedResidueCount_le T v r
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (inversionClass_card_le b)
  rw [hCount]
  calc
    _ ≤ (univ.biUnion S).card := Finset.card_le_card hSubset
    _ ≤ ∑ v, (S v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : T.Node, 2 * n ^ (Fintype.card T.Leaf - 1) := sum_le_sum fun v _ ↦ hSite v
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ac_rfl

private lemma leaf_card_pos (T : RootedTree) : 0 < Fintype.card T.Leaf := by
  have hN : (univ : Finset T.Node).Nonempty := ⟨T.root, mem_univ _⟩
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image univ T.depth hN
  have hLeaf (u : T.Node) (hu : T.parent u = v) : u = v := by
    by_cases h : u = T.root
    · simpa only [h, T.parent_root] using hu
    · have hLt := T.depth_parent_lt u h
      rw [hu] at hLt
      exact False.elim ((not_lt_of_ge (hv u (mem_univ u))) hLt)
  let : Nonempty T.Leaf := ⟨⟨v, hLeaf⟩⟩
  exact Fintype.card_pos

/-- The single-coordinate influence bound for the tree field. -/
theorem average_field_partial_sq_le (T : RootedTree) (k : ZMod n) (b : InversionClass n) :
    average (fun x ↦ walshPartial (T.fieldCoefficient k) b x ^ 2) ≤
      (((2 * T.nodeCount : ℕ) : ℝ) ^ Fintype.card T.Leaf) * (2 * T.nodeCount) / n := by
  let C : ℝ := ((2 * T.nodeCount : ℕ) : ℝ) ^ Fintype.card T.Leaf
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hSite (I : Finset (InversionClass n)) :
      T.fieldCoefficient k I ^ 2 ≤ T.fieldNormalizer n ^ 2 * C * assignmentCount T I := by
    have hN : 0 ≤ T.fieldNormalizer n := by unfold fieldNormalizer; positivity
    have hSq : T.fieldCoefficient k I ^ 2 ≤
        (T.fieldNormalizer n * assignmentCount T I) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hN (by positivity))]
      exact abs_fieldCoefficient_le T k I
    have hCount : (assignmentCount T I : ℝ) ≤ C := by
      dsimp [C]
      exact_mod_cast assignmentCount_le T I
    rw [mul_pow, pow_two (assignmentCount T I : ℝ)] at hSq
    exact hSq.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCount (by positivity)) (sq_nonneg _))
  have hCounts : (∑ I : Finset (InversionClass n), if b ∈ I then
      (assignmentCount T I : ℝ) else 0) ≤ (2 * T.nodeCount) * (n : ℝ) ^ (Fintype.card T.Leaf - 1) := by
    exact_mod_cast assignmentCount_containing_le T b
  rw [average_walshPartial_sq]
  change _ ≤ C * (2 * T.nodeCount) / n
  calc
    _ ≤ ∑ I : Finset (InversionClass n), T.fieldNormalizer n ^ 2 * C *
        (if b ∈ I then (assignmentCount T I : ℝ) else 0) := sum_le_sum fun I _ ↦ by
      by_cases h : b ∈ I
      · simpa only [ite_eq_left h] using hSite I
      · simp [h]
    _ ≤ T.fieldNormalizer n ^ 2 * C *
        ((2 * T.nodeCount) * (n : ℝ) ^ (Fintype.card T.Leaf - 1)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hCounts (mul_nonneg (sq_nonneg _) hC)
    _ = (C * (2 * T.nodeCount) / n) *
        (T.fieldNormalizer n ^ 2 * (n : ℝ) ^ Fintype.card T.Leaf) := by
      have hL : Fintype.card T.Leaf - 1 + 1 = Fintype.card T.Leaf :=
        Nat.sub_add_cancel (leaf_card_pos T)
      conv_rhs => rw [← hL, pow_succ]
      field_simp
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (fieldNormalizer_sq_mul T)

end LovaszTheta.Circulant.RootedTree
