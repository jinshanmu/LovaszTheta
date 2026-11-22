module

public import LovaszTheta.HermiteFieldGrafting
public import LovaszTheta.HermiteTestComparison

/-!
# Single and paired frequency moments of a product

At one regular frequency the Gaussian squared moment is one.
At two regular frequencies distinct up to sign the two Gaussian
families are independent and their product mean is zero.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical Nat

namespace LovaszTheta.Circulant.EvenTreeType

variable {n : ℕ} [NeZero n]

private abbrev Copies (m : EvenTreeType →₀ ℕ) := Bool × m.support

private def copyDegree (m : EvenTreeType →₀ ℕ) (i : Copies m) : ℕ := m i.2.val

private lemma sum_copyDegree (m : EvenTreeType →₀ ℕ) :
    ∑ i, copyDegree m i = 2*m.toMultiset.card := by
  rw [Fintype.sum_prod_type]
  have h (b : Bool) : (∑ i : m.support, copyDegree m (b,i)) = m.toMultiset.card := by
    rw [Finsupp.card_toMultiset,Finsupp.sum]
    exact sum_coe_sort m.support (fun i ↦ m i)
  simp only [h,Fintype.sum_bool,two_mul]

private lemma hermiteField_eq_prod_subtype (m : EvenTreeType →₀ ℕ) (x : InversionClass n → Bool) (k : ZMod n) :
    hermiteField m x k = ∏ i : m.support, normalizedHermite (m i.val) (i.val.representative.field x k) :=
  (prod_coe_sort _ (fun i ↦ normalizedHermite (m i) (i.representative.field x k))).symm

private lemma square_eq_hermiteTest (m : EvenTreeType →₀ ℕ) (f : m.support → ℝ) :
    hermiteTest (Prod.snd : Copies m → m.support) (copyDegree m) f =
      (∏ i : m.support, normalizedHermite (m i.val) (f i))^2 := by
  simp only [hermiteTest, Fintype.prod_prod_type,copyDegree,Fintype.prod_bool,pow_two]

private lemma integral_hermiteTest_square (m : EvenTreeType →₀ ℕ) :
    (∫ x, hermiteTest (Prod.snd : Copies m → m.support) (copyDegree m) x ∂gaussianCoordinates m.support) = 1 := by
  simp_rw [square_eq_hermiteTest,pow_two,← prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun (i : m.support) y ↦ normalizedHermite (m i.val) y*normalizedHermite (m i.val) y)]
  simp only [integral_normalizedHermite_mul,ite_true,prod_const_one]

/-- The regular-frequency squared moment is one up to the comparison error. -/
theorem abs_average_hermiteField_sq_sub_one_le [Nonempty (InversionClass n)]
    (m : EvenTreeType →₀ ℕ) (k : ZMod n) (hk : RegularFrequency k)
    (D M : ℕ) (hD : ∀ i ∈ m.support, i.nodeCount ≤ D) (hM : m.toMultiset.card ≤ M) :
    |average (fun x ↦ hermiteField m x k ^ 2)-1| ≤
      ((2*M)! : ℝ) * (comparisonEnvelope 2 D M / Real.sqrt n) := by
  have h := abs_average_hermiteTest_sub_gaussian_le
    (fun i : m.support ↦ i.val.representative) (fun _ ↦ k) D M
    (fun i ↦ (representative_nodeCount i.val).trans_le (hD i.val i.property)) (fun _ ↦ hk)
    (fun i j e _ ↦ Subtype.ext ((representative_isomorphism_iff j.val i.val).mp e).symm)
    (Prod.snd : Copies m → m.support) (copyDegree m) (by rw [sum_copyDegree]; omega)
  rw [integral_hermiteTest_square] at h
  simpa only [square_eq_hermiteTest,hermiteField_eq_prod_subtype] using h

private def copyFrequency (m : EvenTreeType →₀ ℕ) (k j : ZMod n) (i : Copies m) : ZMod n :=
  if i.1 then j else k

private lemma product_eq_hermiteTest (m : EvenTreeType →₀ ℕ) (x : InversionClass n → Bool) (k j : ZMod n) :
    hermiteTest (id : Copies m → Copies m) (copyDegree m)
      (fun i ↦ i.2.val.representative.field x (copyFrequency m k j i)) =
        hermiteField m x k * hermiteField m x j := by
  simp [hermiteTest,Fintype.prod_prod_type,copyDegree,copyFrequency,
    hermiteField_eq_prod_subtype,mul_comm]

private lemma integral_hermiteTest_product (m : PositiveEvenHermiteIndex EvenTreeType) :
    (∫ x, hermiteTest (id : Copies m.val → Copies m.val) (copyDegree m.val) x
      ∂gaussianCoordinates (Copies m.val)) = 0 := by
  have hSupport : m.val.support.Nonempty := Finsupp.support_nonempty_iff.mpr (fun he ↦ by
    have h := m.property.1
    rw [he,Finsupp.toMultiset_zero,Multiset.card_zero] at h
    exact Nat.lt_irrefl _ h)
  obtain ⟨i,hi⟩ := hSupport
  have h₀ : m.val i ≠ 0 := Finsupp.mem_support_iff.mp hi
  unfold hermiteTest
  simp only [id_eq]
  rw [integral_fintype_prod_eq_prod (fun a : Copies m.val ↦ normalizedHermite (copyDegree m.val a))]
  apply prod_eq_zero (mem_univ (false,⟨i,hi⟩))
  have he := integral_normalizedHermite_mul (m.val i) 0
  simp [h₀,normalizedHermite] at he
  exact he

/-- The product has mean zero up to comparison error at regular frequencies distinct up to sign. -/
theorem abs_average_hermiteField_product_le_regular [Nonempty (InversionClass n)]
    (m : PositiveEvenHermiteIndex EvenTreeType) (k j : ZMod n)
    (hk : RegularFrequency k) (hj : RegularFrequency j) (hkj : j ≠ k ∧ j ≠ -k)
    (D M : ℕ) (hD : ∀ i ∈ m.val.support, i.nodeCount ≤ D) (hM : m.val.toMultiset.card ≤ M) :
    |average (fun x ↦ hermiteField m.val x k * hermiteField m.val x j)| ≤
      ((2*M)! : ℝ) * (comparisonEnvelope 2 D M / Real.sqrt n) := by
  have h := abs_average_hermiteTest_sub_gaussian_le
    (fun i : Copies m.val ↦ i.2.val.representative) (copyFrequency m.val k j) D M
    (fun i ↦ (representative_nodeCount i.2.val).trans_le (hD i.2.val i.2.property))
    (fun i ↦ by unfold copyFrequency; split_ifs <;> assumption)
    (fun a b hiso hFreq ↦ by
      apply Prod.ext
      · rcases a with ⟨u,a⟩
        rcases b with ⟨v,b⟩
        cases u <;> cases v
        · rfl
        · simp only [copyFrequency,Bool.false_eq_true,ite_false,ite_true] at hFreq
          exact (hFreq.elim hkj.1 hkj.2).elim
        · simp only [copyFrequency,Bool.false_eq_true,ite_false,ite_true] at hFreq
          exact (hFreq.elim (fun h ↦ hkj.1 h.symm)
            (fun h ↦ hkj.2 (by rw [h,neg_neg]))).elim
        · rfl
      · exact Subtype.ext ((representative_isomorphism_iff _ _).mp hiso).symm)
    (id : Copies m.val → Copies m.val) (copyDegree m.val) (by rw [sum_copyDegree]; omega)
  simpa only [product_eq_hermiteTest,integral_hermiteTest_product,sub_zero] using h

/-- The absolute product moment is bounded uniformly at every pair of frequencies. -/
theorem abs_average_hermiteField_product_le (m : EvenTreeType →₀ ℕ) (k j : ZMod n) (D M : ℕ)
    (hD : ∀ i ∈ m.support, i.nodeCount ≤ D) (hM : m.toMultiset.card ≤ M) :
    |average (fun x ↦ hermiteField m x k * hermiteField m x j)| ≤ ((2*M)! : ℝ)*comparisonEnvelope 2 D M := by
  refine (abs_average_le_average_abs _).trans ?_
  have h := average_abs_hermiteTest_le
    (fun i : Copies m ↦ i.2.val.representative) (copyFrequency m k j) D M
    (fun i ↦ (representative_nodeCount i.2.val).trans_le (hD i.2.val i.2.property))
    (id : Copies m → Copies m) (copyDegree m) (by rw [sum_copyDegree]; omega)
  simpa only [product_eq_hermiteTest] using h

end LovaszTheta.Circulant.EvenTreeType
