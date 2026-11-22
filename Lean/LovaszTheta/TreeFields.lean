module

public import LovaszTheta.Fourier
public import LovaszTheta.LeafRank
public import LovaszTheta.RandomGraphs

/-!
# Rooted tree fields over a cyclic group

The summation uses an indexed representative of the unordered tree.
Root-preserving parent-map automorphisms provide the normalization.
Every admissible assignment uses distinct nonzero inversion classes.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- A rooted tree with no internal node of outdegree one. The depth
condition makes the parent map acyclic away from the root. -/
structure RootedTree where
  /-- The number of nodes in the tree. -/
  nodeCount : ℕ
  /-- The distinguished root node. -/
  root : Fin nodeCount
  /-- The parent of each node, fixing the root. -/
  parent : Fin nodeCount → Fin nodeCount
  parent_root : parent root = root
  /-- A depth function decreasing along proper parent steps. -/
  depth : Fin nodeCount → ℕ
  depth_parent_lt : ∀ v, v ≠ root → depth (parent v) < depth v
  noUnary : ∀ v, ¬ ∃! u, u ≠ v ∧ parent u = v

namespace RootedTree

/-- The vertex indexing type of a representative. -/
abbrev Node (T : RootedTree) := Fin T.nodeCount

/-- A leaf has no proper child. -/
abbrev Leaf (T : RootedTree) :=
  {v : T.Node // ∀ u : T.Node, T.parent u = v → u = v}

/-- A root-preserving automorphism of the unordered tree. -/
abbrev Automorphism (T : RootedTree) :=
  {e : T.Node ≃ T.Node // e T.root = T.root ∧ Function.Commute e T.parent}

noncomputable instance (T : RootedTree) : Fintype T.Leaf := Fintype.ofFinite _
noncomputable instance (T : RootedTree) : Fintype T.Automorphism := Fintype.ofFinite _

instance (T : RootedTree) : Nonempty T.Automorphism :=
  ⟨⟨Equiv.refl _, rfl, fun _ ↦ rfl⟩⟩

lemma nodeCount_pos (T : RootedTree) : 0 < T.nodeCount := T.root.isLt.pos

/-- Every parent path reaches the root. -/
theorem exists_iterate_parent_eq_root (T : RootedTree) (v : T.Node) :
    ∃ h : ℕ, (T.parent^[h]) v = T.root := by
  induction hv : T.depth v using Nat.strong_induction_on generalizing v with
  | ind m ih =>
    by_cases he : v = T.root
    · exact ⟨0, he⟩
    · have hlt : T.depth (T.parent v) < m := hv ▸ T.depth_parent_lt v he
      obtain ⟨k, hk⟩ := ih _ hlt _ rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk]⟩

/-- The leaves below a node, including the node itself when it is a leaf. -/
noncomputable def descendantLeaves (T : RootedTree) (v : T.Node) : Finset T.Leaf :=
  univ.filter fun u ↦ ∃ h : ℕ, (T.parent^[h]) u.val = v

lemma descendantLeaves_root (T : RootedTree) : T.descendantLeaves T.root = univ := by
  ext u
  simp only [descendantLeaves, mem_filter, mem_univ, true_and, iff_true]
  exact T.exists_iterate_parent_eq_root u.val

lemma descendantLeaves_leaf (T : RootedTree) (u : T.Leaf) :
    T.descendantLeaves u.val = {u} := by
  ext v
  simp only [descendantLeaves, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h, hh⟩
    apply Subtype.ext
    induction h with
    | zero => exact hh
    | succ h ih =>
      rw [Function.iterate_succ_apply'] at hh
      exact ih (u.property _ hh)
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The tree with just its root. -/
def single : RootedTree where
  nodeCount := 1
  root := 0
  parent := id
  parent_root := rfl
  depth := fun _ ↦ 0
  depth_parent_lt := fun _ h ↦ (h (Subsingleton.elim _ _)).elim
  noUnary := fun _ ⟨_, hu, _⟩ ↦ hu.1 (Subsingleton.elim _ _)

variable {n : ℕ}

/-- The residue summed at a node of the tree. -/
noncomputable def residue (T : RootedTree) (a : T.Leaf → ZMod n) (v : T.Node) : ZMod n :=
  ∑ i ∈ T.descendantLeaves v, a i

lemma residue_leaf (T : RootedTree) (a : T.Leaf → ZMod n) (u : T.Leaf) :
    T.residue a u.val = a u := by
  simp [residue, descendantLeaves_leaf]

lemma residue_neg (T : RootedTree) (a : T.Leaf → ZMod n) (v : T.Node) :
    T.residue (-a) v = -T.residue a v := by
  simp [residue, sum_neg_distrib]

/-- The residue assignment is admissible if none of the node sums vanishes
and the inversion classes at distinct nodes are distinct. -/
def Admissible (T : RootedTree) (a : T.Leaf → ZMod n) : Prop :=
  ∃ h : ∀ v, T.residue a v ≠ 0,
    Function.Injective (fun v ↦ inversionClass (T.residue a v) (h v))

/-- The finite type of admissible assignments of residues to the leaves. -/
abbrev Assignment (T : RootedTree) (n : ℕ) :=
  {a : T.Leaf → ZMod n // T.Admissible a}

lemma admissible_neg (T : RootedTree) {a : T.Leaf → ZMod n} (ha : T.Admissible a) :
    T.Admissible (-a) := by
  obtain ⟨hn, hi⟩ := ha
  have hna (v : T.Node) : T.residue (-a) v ≠ 0 := by
    rw [residue_neg]
    exact neg_ne_zero.mpr (hn v)
  have hClass (v : T.Node) :
      inversionClass (T.residue (-a) v) (hna v) = inversionClass (T.residue a v) (hn v) := by
    apply (inversionClass_eq_iff _ _).mpr
    exact Or.inr (residue_neg _ _ _)
  exact ⟨hna, fun u v huv ↦ hi ((hClass u).symm.trans (huv.trans (hClass v)))⟩

/-- Global negation is a permutation on admissible assignments. -/
def negateAssignment (T : RootedTree) (n : ℕ) : T.Assignment n ≃ T.Assignment n :=
  (show Function.Involutive (fun a : T.Assignment n ↦
      ⟨-a.val, T.admissible_neg a.property⟩) by
    intro a
    exact Subtype.ext (neg_neg a.val)).toPerm

/-- The inversion class mapped from a node of an admissible assignment. -/
noncomputable def classEmbedding (T : RootedTree) (a : T.Assignment n) :
    T.Node ↪ InversionClass n where
  toFun v := inversionClass (T.residue a.val v) (a.property.choose v)
  inj' := a.property.choose_spec

/-- The Walsh support of an admissible assignment. -/
noncomputable def signSupport (T : RootedTree) (a : T.Assignment n) :
    Finset (InversionClass n) :=
  univ.map (T.classEmbedding a)

@[simp]
lemma signSupport_card (T : RootedTree) (a : T.Assignment n) :
    (T.signSupport a).card = T.nodeCount := by
  simp [signSupport]

lemma signSupport_negateAssignment (T : RootedTree) (a : T.Assignment n) :
    T.signSupport (T.negateAssignment n a) = T.signSupport a := by
  have hClass : T.classEmbedding (T.negateAssignment n a) = T.classEmbedding a := by
    apply Function.Embedding.ext
    intro v
    let b := T.negateAssignment n a
    exact (inversionClass_eq_iff (b.property.choose v) (a.property.choose v)).mpr
      (Or.inr (residue_neg _ _ _))
  rw [signSupport, signSupport, hClass]

lemma walsh_signSupport (T : RootedTree) (a : T.Assignment n) (x : InversionClass n → Bool) :
    walsh (T.signSupport a) x = ∏ v, epsilon x (T.residue a.val v) := by
  rw [walsh, signSupport, Finset.prod_map]
  exact prod_congr rfl fun v _ ↦ by simp [classEmbedding, epsilon, a.property.choose v]

variable [NeZero n]

noncomputable instance (T : RootedTree) : Fintype (T.Assignment n) := Fintype.ofFinite _

/-- The scalar in the standardized tree field. -/
noncomputable def fieldNormalizer (T : RootedTree) (n : ℕ) : ℝ :=
  (Real.sqrt ((n : ℝ) ^ Fintype.card T.Leaf) * Real.sqrt (Fintype.card T.Automorphism))⁻¹

/-- The complex exponential sum defining the standardized tree field. -/
noncomputable def fieldComplex (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) : ℂ :=
  (T.fieldNormalizer n : ℂ) *
    ∑ a : T.Assignment n, ZMod.stdAddChar (-(T.residue a.val T.root * k)) *
      (walsh (T.signSupport a) x : ℂ)

lemma star_fieldComplex (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) :
    star (T.fieldComplex x k) = T.fieldComplex x k := by
  unfold fieldComplex
  rw [star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm _ (T.fieldNormalizer n : ℂ)]
  congr 1
  rw [map_sum]
  refine Fintype.sum_equiv (T.negateAssignment n) _ _ fun a ↦ ?_
  change star (ZMod.stdAddChar (-(T.residue a.val T.root * k)) *
      (walsh (T.signSupport a) x : ℂ)) =
    ZMod.stdAddChar (-(T.residue (-a.val) T.root * k)) *
      (walsh (T.signSupport (T.negateAssignment n a)) x : ℂ)
  rw [star_mul, star_stdAddChar, signSupport_negateAssignment, residue_neg, neg_mul]
  simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]

/-- The same field as a real cosine sum. -/
noncomputable def field (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  (T.fieldComplex x k).re

lemma ofReal_field (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) :
    (T.field x k : ℂ) = T.fieldComplex x k := by
  have hIm := congrArg Complex.im (star_fieldComplex T x k)
  simp only [Complex.star_def, Complex.conj_im] at hIm
  apply Complex.ext
  · simp [field]
  · simp only [Complex.ofReal_im]
    linarith

lemma field_eq_sum (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) :
    T.field x k = T.fieldNormalizer n *
      ∑ a : T.Assignment n, (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re *
        walsh (T.signSupport a) x := by
  simp [field, fieldComplex, Complex.mul_re, Complex.re_sum]

lemma field_even (T : RootedTree) (x : InversionClass n → Bool) : (T.field x).Even := by
  intro k
  simp only [field_eq_sum]
  congr 1
  apply sum_congr rfl
  intro a _
  rw [mul_neg, ← star_stdAddChar]
  simp

lemma sum_field (T : RootedTree) (x : InversionClass n → Bool) :
    (∑ k, T.field x k) = 0 := by
  simp only [field_eq_sum, ← mul_sum]
  rw [Finset.sum_comm]
  have h (a : T.Assignment n) :
      (∑ k, (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re *
        walsh (T.signSupport a) x) = 0 := by
    rw [← sum_mul]
    have hRoot : -T.residue a.val T.root ≠ 0 := neg_ne_zero.mpr (a.property.choose T.root)
    have hCharacter : (∑ k, (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re) = 0 := by
      simp only [← Complex.re_sum, ← neg_mul, sum_stdAddChar_mul, ite_eq_right hRoot,
        Complex.zero_re]
    rw [hCharacter, zero_mul]
  simp [h]

/-- The coefficients of the distinct sign supports, grouped from the defining sum. -/
noncomputable def fieldCoefficient (T : RootedTree) (k : ZMod n) (I : Finset (InversionClass n)) :
    ℝ :=
  T.fieldNormalizer n * ∑ a : T.Assignment n,
    if T.signSupport a = I then (ZMod.stdAddChar (-(T.residue a.val T.root * k))).re else 0

lemma fieldCoefficient_eq_zero_of_card_ne (T : RootedTree) (k : ZMod n)
    {I : Finset (InversionClass n)} (hI : I.card ≠ T.nodeCount) :
    T.fieldCoefficient k I = 0 := by
  unfold fieldCoefficient
  have h (a : T.Assignment n) : T.signSupport a ≠ I := fun he ↦
    hI (he ▸ T.signSupport_card a)
  simp [h]

lemma field_walsh_expansion (T : RootedTree) (x : InversionClass n → Bool) (k : ZMod n) :
    T.field x k = ∑ I : Finset (InversionClass n), T.fieldCoefficient k I * walsh I x := by
  rw [field_eq_sum]
  unfold fieldCoefficient
  simp only [mul_assoc, ← mul_sum, sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]

end RootedTree

end LovaszTheta.Circulant
