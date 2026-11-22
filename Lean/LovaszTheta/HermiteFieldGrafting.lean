module

public import LovaszTheta.GraftHermiteNormalization
public import LovaszTheta.HermiteGrafting
public import LovaszTheta.HermitePowerExpansion

/-!
# Grafting normalized Hermite products of the fields

The leading power in every Hermite factor is the only tuple
that can reach the node count of the grafted tree. Its factorial
denominator cancels the automorphism factor of the graft.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.EvenTreeType

variable {n : ℕ} [NeZero n]

/-- Evaluation of a Hermite product on the random tree fields. -/
noncomputable def hermiteField (m : EvenTreeType →₀ ℕ) (x : InversionClass n → Bool) (k : ZMod n) : ℝ :=
  hermiteProduct m (fun T ↦ T.representative.field x k)

/-- The indexed occurrences in an arbitrary power tuple. -/
abbrev PowerOccurrences {m : EvenTreeType →₀ ℕ} (q : HermitePowerTuple m) :=
  Σ i : m.support, Fin (q i).val

/-- The original tree type belonging to each occurrence. -/
def powerOccurrenceType {m : EvenTreeType →₀ ℕ} {q : HermitePowerTuple m} (i : PowerOccurrences q) : EvenTreeType :=
  i.1.val

private lemma familyMultiset_eq_sum_singletons {I A : Type*} [Fintype I] (f : I → A) :
    familyMultiset f = ∑ i, ({f i} : Multiset A) := by
  unfold familyMultiset
  rw [← sum_multiset_singleton (univ : Finset I)]
  change (Multiset.mapAddMonoidHom f) (∑ i : I, ({i} : Multiset I)) = _
  simp only [map_sum,Multiset.coe_mapAddMonoidHom,Multiset.map_singleton]

lemma familyMultiset_leadingOccurrences (m : EvenTreeType →₀ ℕ) :
    familyMultiset (powerOccurrenceType (q := leadingHermitePowerTuple m)) = m.toMultiset := by
  rw [familyMultiset_eq_sum_singletons,Fintype.sum_sigma,Finsupp.toMultiset_apply]
  have h (i : m.support) :
      (∑ a : Fin (leadingHermitePowerTuple m i).val, ({powerOccurrenceType ⟨i,a⟩} : Multiset EvenTreeType)) =
        m i.val • ({i.val} : Multiset EvenTreeType) := by
    change (∑ _ : Fin (m i.val), ({i.val} : Multiset EvenTreeType)) = _
    simp
  simp only [h]
  exact sum_coe_sort m.support (fun i ↦ m i • ({i} : Multiset EvenTreeType))

private lemma leadingOccurrences_card (m : EvenTreeType →₀ ℕ) :
    Fintype.card (PowerOccurrences (leadingHermitePowerTuple m)) = m.toMultiset.card := by
  rw [← familyMultiset_leadingOccurrences,card_familyMultiset]

private lemma hermiteField_eq_sum_powerOccurrences (m : EvenTreeType →₀ ℕ)
    (x : InversionClass n → Bool) (k : ZMod n) :
    hermiteField m x k = ∑ q : HermitePowerTuple m, hermiteProductPowerCoeff m q *
      ∏ a : PowerOccurrences q, (powerOccurrenceType a).representative.field x k := by
  unfold hermiteField hermiteProduct
  rw [prod_normalizedHermite_eq_sum_powers]
  refine sum_congr rfl fun q _ ↦ ?_
  congr 1
  rw [Fintype.prod_sigma]
  simp only [powerOccurrenceType,prod_const,card_univ,Fintype.card_fin]

lemma nodeCount_graftOfIndex (m : PositiveEvenHermiteIndex EvenTreeType) :
    (graftOfIndex m).nodeCount = 1+∑ i : m.val.support, m.val i.val * i.val.representative.nodeCount := by
  let f : PowerOccurrences (leadingHermitePowerTuple m.val) → EvenTreeType := powerOccurrenceType
  have h : Even (Fintype.card (PowerOccurrences (leadingHermitePowerTuple m.val))) :=
    (leadingOccurrences_card m.val).symm ▸ m.property.2
  have he := nodeCount_graft f h
  have hTree : graft (familyMultiset f) (by rwa [card_familyMultiset]) = graftOfIndex m := by
    apply children_injective
    apply Subtype.ext
    rw [children_graft,children_graftOfIndex]
    exact familyMultiset_leadingOccurrences _
  rw [hTree,Fintype.sum_sigma] at he
  rw [he]
  congr 1
  apply sum_congr rfl
  intro i _
  change (∑ _ : Fin (m.val i.val), i.val.nodeCount) = m.val i.val * i.val.representative.nodeCount
  simp [representative_nodeCount]

private lemma powerOccurrences_degree_lt {m : PositiveEvenHermiteIndex EvenTreeType}
    (q : HermitePowerTuple m.val) (hq : q ≠ leadingHermitePowerTuple m.val) :
    1 + ∑ a : PowerOccurrences q, (powerOccurrenceType a).representative.nodeCount <
      (graftOfIndex m).representative.nodeCount := by
  rw [representative_nodeCount,nodeCount_graftOfIndex,Fintype.sum_sigma]
  simp only [powerOccurrenceType,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Nat.add_lt_add_left
  obtain ⟨i,hi⟩ : ∃ i, (q i).val < m.val i.val := by
    by_contra h
    push Not at h
    apply hq
    funext i
    exact Fin.ext (le_antisymm (Nat.le_of_lt_succ (q i).isLt) (h i))
  exact sum_lt_sum (fun z _ ↦ Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (q z).isLt))
    ⟨i,mem_univ i,Nat.mul_lt_mul_of_pos_right hi i.val.representative.nodeCount_pos⟩

private lemma leadingOccurrences_projection (m : PositiveEvenHermiteIndex EvenTreeType) (k : ZMod n) :
    hermiteProductPowerCoeff m.val (leadingHermitePowerTuple m.val) •
      walshDegree (graftOfIndex m).representative.nodeCount (fun x ↦ signOperator x
        (fun j ↦ ∏ a : PowerOccurrences (leadingHermitePowerTuple m.val),
          (powerOccurrenceType a).representative.field x j) k) =
      fun x ↦ (graftOfIndex m).representative.field x k := by
  let I := PowerOccurrences (leadingHermitePowerTuple m.val)
  let f : I → EvenTreeType := powerOccurrenceType
  let S (i : I) := (f i).representative
  have hCard : Fintype.card I = m.val.toMultiset.card := leadingOccurrences_card m.val
  have hI : Even (Fintype.card I) := hCard.symm ▸ m.property.2
  have hNe : Fintype.card I ≠ 1 := by obtain ⟨r,hr⟩ := hI; omega
  let _ : Nonempty I := Fintype.card_pos_iff.mp (hCard.symm ▸ m.property.1)
  obtain ⟨e⟩ := graft_isomorphism f hI
  have hG : graft (familyMultiset f) (by rwa [card_familyMultiset]) = graftOfIndex m := by
    apply children_injective
    apply Subtype.ext
    rw [children_graft,children_graftOfIndex]
    exact familyMultiset_leadingOccurrences _
  rw [hG] at e
  have hN : (RootedTree.graft S hNe).nodeCount = (graftOfIndex m).representative.nodeCount := e.nodeCount_eq
  have hh : (∏ i, (S i).fieldNormalizer n) / (RootedTree.graft S hNe).fieldNormalizer n =
      ∏ i : m.val.support, Real.sqrt (m.val i.val).factorial := by
    rw [RootedTree.fieldNormalizer_graft_ratio S hNe f (fun i j ↦ representative_isomorphism_iff _ _)]
    change (∏ a ∈ (familyMultiset (powerOccurrenceType (q := leadingHermitePowerTuple m.val))).toFinset,
      Real.sqrt ((familyMultiset (powerOccurrenceType (q := leadingHermitePowerTuple m.val))).count a).factorial) = _
    rw [familyMultiset_leadingOccurrences,Finsupp.toFinset_toMultiset]
    simp only [Finsupp.count_toMultiset]
    exact (prod_coe_sort _ (fun i ↦ Real.sqrt (m.val i).factorial)).symm
  change hermiteProductPowerCoeff m.val (leadingHermitePowerTuple m.val) •
    walshDegree _ (fun x ↦ signOperator x (fun j ↦ ∏ a, (S a).field x j) k) = _
  rw [← hN,RootedTree.walshDegree_signOperator_treeProduct S hNe,hh,hermiteProductPowerCoeff_leading,
    smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
  funext x
  exact e.field_eq x k

/-- The highest-degree part is exactly the new tree field. -/
theorem walshDegree_signOperator_hermiteField (m : PositiveEvenHermiteIndex EvenTreeType) (k : ZMod n) :
    walshDegree (graftOfIndex m).representative.nodeCount (fun x ↦ signOperator x (hermiteField m.val x) k) =
      fun x ↦ (graftOfIndex m).representative.field x k := by
  let term (q : HermitePowerTuple m.val) := fun (x : InversionClass n → Bool) ↦
    signOperator x (fun j ↦ ∏ a : PowerOccurrences q, (powerOccurrenceType a).representative.field x j) k
  have he : (fun x ↦ signOperator x (hermiteField m.val x) k) =
      ∑ q : HermitePowerTuple m.val, hermiteProductPowerCoeff m.val q • term q := by
    funext x
    have hV : hermiteField m.val x =
        ∑ q : HermitePowerTuple m.val, hermiteProductPowerCoeff m.val q •
          (fun j ↦ ∏ a : PowerOccurrences q, (powerOccurrenceType a).representative.field x j) := by
      funext j
      simp only [hermiteField_eq_sum_powerOccurrences,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [hV,map_sum]
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,term]
  rw [he,map_sum,Fintype.sum_eq_single (leadingHermitePowerTuple m.val)]
  · rw [map_smul]
    exact leadingOccurrences_projection m k
  · intro q hq
    rw [map_smul]
    have hz := RootedTree.walshDegree_signOperator_treeProduct_eq_zero
      (fun a : PowerOccurrences q ↦ (powerOccurrenceType a).representative) k (powerOccurrences_degree_lt q hq)
    rw [show walshDegree (graftOfIndex m).representative.nodeCount (term q) = 0 from hz,smul_zero]

/-- Orthogonality removes the cross term between the graft and the residual. -/
theorem average_sq_graftResidual (m : PositiveEvenHermiteIndex EvenTreeType) (k : ZMod n) :
    average (fun x ↦ (signOperator x (hermiteField m.val x) k - (graftOfIndex m).representative.field x k)^2) =
      average (fun x ↦ (signOperator x (hermiteField m.val x) k)^2) -
        average (fun x ↦ (graftOfIndex m).representative.field x k ^ 2) := by
  have h := average_sq_sub_walshDegree (graftOfIndex m).representative.nodeCount
    (fun x ↦ signOperator x (hermiteField m.val x) k)
  rwa [walshDegree_signOperator_hermiteField] at h

end LovaszTheta.Circulant.EvenTreeType
