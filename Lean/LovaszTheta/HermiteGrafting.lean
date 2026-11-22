module

public import LovaszTheta.GaussianTreeCoefficients
public import LovaszTheta.HermiteProducts

/-!
# The Gaussian grafting isometry

Grafting bijects the positive even Hermite indices with the
nonleaf tree types. Both indexed families are orthonormal, so
their square-summable series define an isometry on the closed span.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Classical ENNReal RealInnerProductSpace

namespace LovaszTheta.Circulant

section Hilbert

variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {v : J → E}

/-- The isometry that sums square-summable coefficients against an orthonormal family. -/
noncomputable def orthonormalSeries (h : Orthonormal ℝ v) : lp (fun _ : J ↦ ℝ) 2 →ₗᵢ[ℝ] E :=
  h.orthogonalFamily.linearIsometry

lemma hasSum_orthonormalSeries (h : Orthonormal ℝ v) (a : lp (fun _ : J ↦ ℝ) 2) :
    HasSum (fun i ↦ a i • v i) (orthonormalSeries h a) :=
  h.orthogonalFamily.hasSum_linearIsometry a

lemma inner_orthonormalSeries (h : Orthonormal ℝ v) (a : lp (fun _ : J ↦ ℝ) 2) (i : J) :
    ⟪orthonormalSeries h a,v i⟫ = a i := by
  have hs := (hasSum_orthonormalSeries h a).mapL (innerSL ℝ (v i))
  have hp (j : J) : ⟪v i,a j • v j⟫ = if i = j then a i else 0 := by
    rw [real_inner_smul_right,orthonormal_iff_ite.mp h]
    by_cases hj : i = j <;> simp [hj]
  rw [real_inner_comm]
  change innerSL ℝ (v i) (orthonormalSeries h a) = _
  rw [← hs.tsum_eq]
  simp only [innerSL_apply_apply,hp]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    rw [ite_eq_right hj.symm]

@[simp]
lemma orthonormalSeries_single [DecidableEq J] (h : Orthonormal ℝ v) (i : J) (a : ℝ) :
    orthonormalSeries h (lp.single 2 i a) = a • v i := by
  rw [orthonormalSeries, OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply]

lemma range_orthonormalSeries (h : Orthonormal ℝ v) :
    (orthonormalSeries h).toLinearMap.range = (Submodule.span ℝ (Set.range v)).topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hasSum_orthonormalSeries h a)
      (Filter.Eventually.of_forall fun s ↦ Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)))
  · apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (orthonormalSeries h).isometry.isClosedEmbedding.isClosed_range
    rintro _ ⟨i,rfl⟩
    exact ⟨lp.single 2 i 1,by simp⟩

end Hilbert

variable {I : Type*}

/-- The coordinate random variable in the product Gaussian Hilbert space. -/
noncomputable def gaussianCoordinateL2 (i : I) : Lp ℝ 2 (gaussianProduct I) :=
  hermiteProductL2 (Finsupp.single i 1)

lemma gaussianCoordinateL2_ae_eq (i : I) :
    gaussianCoordinateL2 i =ᵐ[gaussianProduct I] fun x ↦ x i := by
  refine (hermiteProductL2_ae_eq (Finsupp.single i 1)).trans (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [hermiteProduct, normalizedHermite, Finsupp.support_single]

theorem orthonormal_gaussianCoordinateL2 : Orthonormal ℝ (gaussianCoordinateL2 (I := I)) :=
  orthonormal_hermiteProductL2.comp _ (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0))

/-- The Gaussian linear combination, converging in L². -/
noncomputable def gaussianSeries (I : Type*) :
    lp (fun _ : I ↦ ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct I) :=
  orthonormalSeries orthonormal_gaussianCoordinateL2

/-- Multivariate Hermite indices of positive even degree. -/
abbrev PositiveEvenHermiteIndex (I : Type*) :=
  {m : I →₀ ℕ // 0 < m.toMultiset.card ∧ Even m.toMultiset.card}

namespace EvenTreeType

/-- Add the root to the multiset of the Hermite index. -/
noncomputable def graftOfIndex (m : PositiveEvenHermiteIndex EvenTreeType) : EvenTreeType :=
  graft m.val.toMultiset m.property.2

lemma children_graftOfIndex (m : PositiveEvenHermiteIndex EvenTreeType) :
    (children (graftOfIndex m)).val = m.val.toMultiset :=
  congrArg Subtype.val (children_graft _ _)

lemma graftOfIndex_ne_leaf (m : PositiveEvenHermiteIndex EvenTreeType) :
    graftOfIndex m ≠ leaf := by
  intro he
  have h := congrArg (fun T ↦ (children T).val) he
  rw [children_graftOfIndex,children_leaf] at h
  exact (Nat.ne_of_gt m.property.1) (by simp [h])

lemma graftOfIndex_injective : Function.Injective graftOfIndex := by
  intro m q h
  have he := congrArg (fun T ↦ (children T).val) h
  rw [children_graftOfIndex,children_graftOfIndex] at he
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  simpa only [Finsupp.count_toMultiset] using congrArg (Multiset.count i) he

/-- Positive even multi-indices correspond bijectively to the nonleaf tree types. -/
noncomputable def graftOfIndexEquiv :
    PositiveEvenHermiteIndex EvenTreeType ≃ {T : EvenTreeType // T ≠ leaf} :=
  Equiv.ofBijective (fun m ↦ ⟨graftOfIndex m,graftOfIndex_ne_leaf m⟩) (by
    constructor
    · intro m q h
      exact graftOfIndex_injective (congrArg Subtype.val h)
    · rintro ⟨T,hT⟩
      let m := (children T).val.toFinsupp
      have hm : m.toMultiset = (children T).val := Multiset.toFinsupp_toMultiset _
      have hPos : 0 < (children T).val.card := by
        by_contra h
        have h₀ : (children T).val = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
        exact hT (children_injective (Subtype.ext (h₀.trans children_leaf.symm)))
      let q : PositiveEvenHermiteIndex EvenTreeType := ⟨m,by rw [hm]; exact ⟨hPos,(children T).property⟩⟩
      refine ⟨q,Subtype.ext (children_injective (Subtype.ext ?_))⟩
      exact (children_graftOfIndex q).trans hm)

/-- The summation isometry of the Hermite products of positive even degree. -/
noncomputable def evenHermiteSeries :
    lp (fun _ : PositiveEvenHermiteIndex EvenTreeType ↦ ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct EvenTreeType) :=
  orthonormalSeries (orthonormal_hermiteProductL2.comp _ Subtype.val_injective)

/-- The summation isometry of coordinates indexed by grafted tree types. -/
noncomputable def graftedSeries :
    lp (fun _ : PositiveEvenHermiteIndex EvenTreeType ↦ ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct EvenTreeType) :=
  orthonormalSeries (orthonormal_gaussianCoordinateL2.comp _ graftOfIndex_injective)

/-- The grafting map on the closed span of the positive even Hermite products. -/
noncomputable def gaussianGraftIsometry : evenHermiteSeries.toLinearMap.range →ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianProduct EvenTreeType) :=
  graftedSeries.comp evenHermiteSeries.equivRange.symm.toLinearIsometry

theorem evenHermiteSeries_range : evenHermiteSeries.toLinearMap.range =
    (Submodule.span ℝ (Set.range (fun m : PositiveEvenHermiteIndex EvenTreeType ↦
      hermiteProductL2 m.val))).topologicalClosure :=
  range_orthonormalSeries _

theorem graftedSeries_range : graftedSeries.toLinearMap.range =
    (Submodule.span ℝ (Set.range (fun T : {T : EvenTreeType // T ≠ leaf} ↦
      gaussianCoordinateL2 T.val))).topologicalClosure := by
  rw [graftedSeries,range_orthonormalSeries]
  congr 2
  exact graftOfIndexEquiv.surjective.range_comp (fun T : {T : EvenTreeType // T ≠ leaf} ↦ gaussianCoordinateL2 T.val)

lemma gaussianGraftIsometry_series (a : lp (fun _ : PositiveEvenHermiteIndex EvenTreeType ↦ ℝ) 2) :
    gaussianGraftIsometry (evenHermiteSeries.equivRange a) = graftedSeries a := by
  simp [gaussianGraftIsometry]

lemma evenHermiteSeries_single (m : PositiveEvenHermiteIndex EvenTreeType) :
    evenHermiteSeries (lp.single 2 m 1) = hermiteProductL2 m.val :=
  (orthonormalSeries_single (orthonormal_hermiteProductL2.comp _ Subtype.val_injective) m 1).trans (one_smul _ _)

/-- On an individual Hermite product, the isometry returns the grafted coordinate. -/
theorem gaussianGraftIsometry_hermiteProduct (m : PositiveEvenHermiteIndex EvenTreeType) :
    gaussianGraftIsometry ⟨hermiteProductL2 m.val,⟨lp.single 2 m 1,evenHermiteSeries_single m⟩⟩ =
      gaussianCoordinateL2 (graftOfIndex m) := by
  have h : (⟨hermiteProductL2 m.val,⟨lp.single 2 m 1,evenHermiteSeries_single m⟩⟩ :
        evenHermiteSeries.toLinearMap.range) = evenHermiteSeries.equivRange (lp.single 2 m 1) := by
    apply Subtype.ext
    exact (evenHermiteSeries_single m).symm
  rw [h,gaussianGraftIsometry_series]
  exact (orthonormalSeries_single (orthonormal_gaussianCoordinateL2.comp _ graftOfIndex_injective) m 1).trans
    (one_smul _ _)

end EvenTreeType

end LovaszTheta.Circulant
