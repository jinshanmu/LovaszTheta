module

public import LovaszTheta.GaussianEquation
public import LovaszTheta.LeafField

/-!
# Size truncation of the Gaussian solution

The truncated variance contains the leaf coefficient of two
and is bounded by the variance of the full Gaussian. The
mean-square truncation error is the branching population tail.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace LovaszTheta.Circulant.EvenTreeType

@[simp]
lemma nodeCount_leaf : leaf.nodeCount = 1 := by
  let f (_ : Fin 0) := leaf
  have h := nodeCount_graft f (by simp)
  have hf : familyMultiset f = 0 := Multiset.card_eq_zero.mp (by simp [card_familyMultiset])
  have hG : graft (familyMultiset f) (by simp [hf]) = leaf := by
    apply children_injective
    apply Subtype.ext
    rw [children_graft,children_leaf]
    exact hf
  rw [hG] at h
  simpa only [Finset.univ_eq_empty,Finset.sum_empty,add_zero] using h

/-- The designated unordered leaf is isomorphic to the one-node representative. -/
noncomputable def leafIsomorphismSingle : leaf.representative.Isomorphism RootedTree.single :=
  ⟨finCongr (leaf.representative_nodeCount.trans nodeCount_leaf),Subsingleton.elim _ _,fun _ ↦ Subsingleton.elim _ _⟩

/-- All unordered tree types through a prescribed size. -/
noncomputable def typesThroughSize (D : ℕ) : Finset EvenTreeType :=
  (univ : Finset {T : EvenTreeType // T.nodeCount ≤ D}).map ⟨Subtype.val,Subtype.val_injective⟩

lemma mem_typesThroughSize (T : EvenTreeType) (D : ℕ) :
    T ∈ typesThroughSize D ↔ T.nodeCount ≤ D := by
  unfold typesThroughSize
  simp only [mem_map,mem_univ,true_and,Function.Embedding.coeFn_mk,Subtype.exists]
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact hS
  · intro hT
    exact ⟨T,hT,rfl⟩

lemma card_typesThroughSize_le (D : ℕ) : (typesThroughSize D).card ≤ 4^D := by
  simpa only [typesThroughSize,card_map,card_univ] using card_nodeCount_le D

variable {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
  (hMean : activationMean τ σ = 2*Real.sqrt (1+τ))

/-- The finite Gaussian sum supported on trees of at most D nodes. -/
noncomputable def gaussianSizeProjection (D : ℕ) : Lp ℝ 2 (gaussianProduct EvenTreeType) :=
  σ • gaussianSeries EvenTreeType (truncateCoefficients (gaussianCoefficientVector hτ hσ hσ' hMean) (typesThroughSize D))

lemma gaussianSizeProjection_ae_eq (D : ℕ) :
    gaussianSizeProjection hτ hσ hσ' hMean D =ᵐ[gaussianProduct EvenTreeType]
      fun x ↦ ∑ T ∈ typesThroughSize D, (σ * gaussianCoefficient τ σ T) * x T := by
  let u := gaussianCoefficientVector hτ hσ hσ' hMean
  apply (Lp.coeFn_smul σ (gaussianSeries EvenTreeType (truncateCoefficients u (typesThroughSize D)))).trans
  have h := gaussianSeries_finsetSum_ae (typesThroughSize D) u
  exact h.mono fun x hx ↦ by
    change σ • gaussianSeries EvenTreeType (truncateCoefficients u (typesThroughSize D)) x =
      ∑ T ∈ typesThroughSize D, (σ * gaussianCoefficient τ σ T) * x T
    rw [smul_eq_mul,show gaussianSeries EvenTreeType (truncateCoefficients u (typesThroughSize D)) x =
      ∑ T ∈ typesThroughSize D, u T*x T from hx,mul_sum]
    simp only [u,gaussianCoefficientVector_apply,mul_assoc]

lemma norm_sq_gaussianSizeProjection (D : ℕ) :
    ‖gaussianSizeProjection hτ hσ hσ' hMean D‖^2 =
      σ^2*∑ T ∈ typesThroughSize D, gaussianCoefficient τ σ T ^ 2 := by
  let u := gaussianCoefficientVector hτ hσ hσ' hMean
  unfold gaussianSizeProjection
  rw [norm_smul,(gaussianSeries EvenTreeType).norm_map,mul_pow,Real.norm_eq_abs,sq_abs]
  congr 1
  rw [← sum_sq_eq_gaussianCoefficient_norm_sq (s := typesThroughSize D) (a := truncateCoefficients u (typesThroughSize D))
    (fun T hT ↦ by rw [truncateCoefficients_apply,ite_eq_right hT])]
  exact sum_congr rfl fun T hT ↦ by
    rw [truncateCoefficients_apply,ite_eq_left hT,gaussianCoefficientVector_apply]

/-- Lower and upper bounds on the variance of the finite projection. -/
theorem gaussianSizeProjection_variance_bounds {D : ℕ} (hD : 0 < D) :
    4 ≤ ‖gaussianSizeProjection hτ hσ hσ' hMean D‖^2 ∧
      ‖gaussianSizeProjection hτ hσ hσ' hMean D‖^2 ≤ 2*Real.pi := by
  rw [norm_sq_gaussianSizeProjection]
  have hLeaf : leaf ∈ typesThroughSize D := (mem_typesThroughSize leaf D).mpr (by
    rw [nodeCount_leaf]
    exact Nat.succ_le_of_lt hD)
  constructor
  · have he : σ^2 * gaussianCoefficient τ σ leaf ^ 2 = 4 := by
      rw [gaussianCoefficient_leaf]
      field_simp
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_left (single_le_sum (fun T _ ↦ sq_nonneg (gaussianCoefficient τ σ T)) hLeaf) (sq_nonneg σ)
  · have hS := hasSum_gaussianCoefficient_sq hτ hσ hσ' hMean
    have hLe : ∑ T ∈ typesThroughSize D, gaussianCoefficient τ σ T ^ 2 ≤ 1 :=
      (hS.summable.sum_le_tsum _ (fun T _ ↦ sq_nonneg (gaussianCoefficient τ σ T))).trans_eq hS.tsum_eq
    refine (mul_le_of_le_one_right (sq_nonneg σ) hLe).trans ?_
    exact (pow_le_pow_left₀ hσ.le hσ' 2).trans_eq (Real.sq_sqrt (by positivity))

/-- The Gaussian scale of the size-truncated sum. -/
noncomputable def gaussianSizeScale (D : ℕ) : ℝ :=
  σ * ‖truncateCoefficients (gaussianCoefficientVector hτ hσ hσ' hMean) (typesThroughSize D)‖

/-- The unit vector along the size-truncated Gaussian sum. -/
noncomputable def gaussianSizeDirection (D : ℕ) : lp (fun _ : EvenTreeType ↦ ℝ) 2 :=
  normalizedTruncation (gaussianCoefficientVector hτ hσ hσ' hMean) (typesThroughSize D)

lemma gaussianSizeScale_eq_norm (D : ℕ) :
    gaussianSizeScale hτ hσ hσ' hMean D = ‖gaussianSizeProjection hτ hσ hσ' hMean D‖ := by
  rw [gaussianSizeProjection,norm_smul,(gaussianSeries EvenTreeType).norm_map,Real.norm_eq_abs,abs_of_pos hσ]
  rfl

lemma gaussianSizeScale_bounds {D : ℕ} (hD : 0 < D) :
    2 ≤ gaussianSizeScale hτ hσ hσ' hMean D ∧
      gaussianSizeScale hτ hσ hσ' hMean D ≤ Real.sqrt (2*Real.pi) := by
  rw [gaussianSizeScale_eq_norm]
  obtain ⟨h₁,h₂⟩ := gaussianSizeProjection_variance_bounds hτ hσ hσ' hMean hD
  have h : (2 : ℝ)^2 = 4 := by norm_num
  exact ⟨le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (norm_nonneg _) (h ▸ h₁),
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr h₂⟩

lemma norm_truncateCoefficients_pos {D : ℕ} (hD : 0 < D) :
    0 < ‖truncateCoefficients (gaussianCoefficientVector hτ hσ hσ' hMean) (typesThroughSize D)‖ := by
  have h := (gaussianSizeScale_bounds hτ hσ hσ' hMean hD).1
  unfold gaussianSizeScale at h
  by_contra! hn
  have hz := le_antisymm hn (norm_nonneg _)
  rw [hz,mul_zero] at h
  norm_num at h

lemma norm_gaussianSizeDirection {D : ℕ} (hD : 0 < D) :
    ‖gaussianSizeDirection hτ hσ hσ' hMean D‖ = 1 := by
  have h := norm_truncateCoefficients_pos hτ hσ hσ' hMean hD
  unfold gaussianSizeDirection normalizedTruncation
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ h.ne']

lemma gaussianSizeDirection_apply_of_notMem (D : ℕ) (T : EvenTreeType) (hT : T ∉ typesThroughSize D) :
    gaussianSizeDirection hτ hσ hσ' hMean D T = 0 :=
  normalizedTruncation_apply_of_notMem _ _ T hT

lemma gaussianSizeScale_mul_direction {D : ℕ} (hD : 0 < D) (T : EvenTreeType) (hT : T ∈ typesThroughSize D) :
    gaussianSizeScale hτ hσ hσ' hMean D * gaussianSizeDirection hτ hσ hσ' hMean D T =
      σ * gaussianCoefficient τ σ T := by
  have h := norm_truncateCoefficients_pos hτ hσ hσ' hMean hD
  unfold gaussianSizeScale gaussianSizeDirection normalizedTruncation
  rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,← mul_assoc,mul_assoc σ,mul_inv_cancel₀ h.ne',
    mul_one,truncateCoefficients_apply,ite_eq_left hT,gaussianCoefficientVector_apply]

lemma gaussianSizeScale_smul_series {D : ℕ} (hD : 0 < D) :
    gaussianSizeScale hτ hσ hσ' hMean D • gaussianSeries EvenTreeType (gaussianSizeDirection hτ hσ hσ' hMean D) =
      gaussianSizeProjection hτ hσ hσ' hMean D := by
  have h := norm_truncateCoefficients_pos hτ hσ hσ' hMean hD
  unfold gaussianSizeScale gaussianSizeDirection normalizedTruncation gaussianSizeProjection
  rw [map_smul,smul_smul,mul_assoc,mul_inv_cancel₀ h.ne',mul_one]

/-- The removed Gaussian variance equals the tail of the squared tree coefficients. -/
lemma norm_sq_gaussianSizeProjection_sub (D : ℕ) :
    ‖σ • gaussianSeries EvenTreeType (gaussianCoefficientVector hτ hσ hσ' hMean) -
      gaussianSizeProjection hτ hσ hσ' hMean D‖^2 =
      σ^2 * ∑' T : EvenTreeType, if D < T.nodeCount then gaussianCoefficient τ σ T ^ 2 else 0 := by
  let u := gaussianCoefficientVector hτ hσ hσ' hMean
  unfold gaussianSizeProjection
  rw [← smul_sub, ← map_sub, norm_smul, (gaussianSeries EvenTreeType).norm_map, mul_pow,Real.norm_eq_abs,sq_abs]
  congr 1
  rw [← (hasSum_gaussianCoefficient_norm_sq _).tsum_eq]
  apply tsum_congr
  intro T
  have hmem := mem_typesThroughSize T D
  change (u T - truncateCoefficients u (typesThroughSize D) T)^2 = _
  rw [truncateCoefficients_apply]
  by_cases hT : D < T.nodeCount
  · rw [ite_eq_right (mt hmem.mp (not_le_of_gt hT)),ite_eq_left hT,sub_zero,gaussianCoefficientVector_apply]
  · rw [ite_eq_left (hmem.mpr (le_of_not_gt hT)),ite_eq_right hT,sub_self,zero_pow (by decide)]

/-- The population moments give polynomial decay of every order for the truncation error. -/
theorem gaussianSizeProjection_error_le {D : ℕ} (hD : 0 < D) (p : ℕ) :
    ‖σ • gaussianSeries EvenTreeType (gaussianCoefficientVector hτ hσ hσ' hMean) -
      gaussianSizeProjection hτ hσ hσ' hMean D‖^2 ≤
      σ^2 * (∑' T : EvenTreeType, gaussianCoefficient τ σ T ^ 2 * (T.nodeCount : ℝ)^p) / (D : ℝ)^p := by
  rw [norm_sq_gaussianSizeProjection_sub,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (gaussianCoefficient_sq_tail_le hτ hσ hσ' hMean hD p) (sq_nonneg σ)

end LovaszTheta.Circulant.EvenTreeType
