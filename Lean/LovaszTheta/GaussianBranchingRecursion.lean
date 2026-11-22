module

public import LovaszTheta.GaussianTreeCoefficients
public import LovaszTheta.HermiteGrafting
public import LovaszTheta.HermiteGenerating
public import LovaszTheta.GaussianTruncation

/-!
# Coefficients of the Gaussian equation

The branching probabilities normalize the coefficient vector.
At every nonleaf root the coefficient of the grafted coordinate
is the corresponding multivariate Hermite coefficient.
-/

@[expose] public section

open Finset
open scoped Classical Nat ENNReal

namespace LovaszTheta.Circulant.EvenTreeType

/-- The unit Gaussian coefficient vector supplied by the branching process. -/
noncomputable def gaussianCoefficientVector {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    lp (fun _ : EvenTreeType ↦ ℝ) 2 :=
  ⟨gaussianCoefficient τ σ,memℓp_gen (by
    have h := (hasSum_gaussianCoefficient_sq hτ hσ hσ' hMean).summable
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using h)⟩

lemma gaussianCoefficientVector_apply {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) (T : EvenTreeType) :
    gaussianCoefficientVector hτ hσ hσ' hMean T = gaussianCoefficient τ σ T := rfl

lemma norm_gaussianCoefficientVector {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    ‖gaussianCoefficientVector hτ hσ hσ' hMean‖ = 1 := by
  have h := hasSum_gaussianCoefficient_norm_sq (gaussianCoefficientVector hτ hσ hσ' hMean)
  simp only [gaussianCoefficientVector_apply] at h
  have he := h.unique (hasSum_gaussianCoefficient_sq hτ hσ hσ' hMean)
  nlinarith [norm_nonneg (gaussianCoefficientVector hτ hσ hσ' hMean)]

/-- The coefficient recursion in the Hermite index parametrization. -/
theorem gaussianCoefficient_graftOfIndex (τ σ : ℝ) (hσ : σ ≠ 0) (m : PositiveEvenHermiteIndex EvenTreeType) :
    σ * gaussianCoefficient τ σ (graftOfIndex m) =
      activationCoefficient τ σ m.val.toMultiset.card * hermiteLinearCoeff (gaussianCoefficient τ σ) m.val := by
  let T := graftOfIndex m
  let f (i : Fin T.childList.length) := T.childList[i]
  have hF : familyMultiset f = m.val.toMultiset := by
    rw [show familyMultiset f = (T.childList : Multiset EvenTreeType) from familyMultiset_get _,childList,
      Multiset.coe_toList,children_graftOfIndex]
  have hCard := congrArg Multiset.card hF
  rw [card_familyMultiset,Fintype.card_fin] at hCard
  have hOrd := card_familyOrdering_mul f
  rw [hF,Finsupp.toFinset_toMultiset,Fintype.card_fin] at hOrd
  simp only [Finsupp.count_toMultiset] at hOrd
  have hSpec := Nat.multinomial_spec m.val.support m.val
  have hSum : ∑ i ∈ m.val.support, m.val i = m.val.toMultiset.card := by
    rw [Finsupp.card_toMultiset,Finsupp.sum]
    rfl
  rw [hSum, ← Finsupp.multinomial_eq,mul_comm] at hSpec
  have hO : Fintype.card (FamilyOrdering f) = m.val.multinomial :=
    Nat.eq_of_mul_eq_mul_right (by positivity) ((hOrd.trans (congrArg Nat.factorial hCard)).trans hSpec.symm)
  have hProd : (∏ i, gaussianCoefficient τ σ (f i)) = ∏ i ∈ m.val.support, gaussianCoefficient τ σ i^(m.val i) := by
    calc
      _ = ((familyMultiset f).map (gaussianCoefficient τ σ)).prod := by
        simp only [familyMultiset,Multiset.map_map,Finset.prod]
        rfl
      _ = _ := by
        rw [hF,prod_multiset_map_count,Finsupp.toFinset_toMultiset]
        simp only [Finsupp.count_toMultiset]
  change σ * gaussianCoefficient τ σ T = _
  rw [gaussianCoefficient]
  change σ * (offspringAmplitude τ σ T.childList.length * Real.sqrt (Fintype.card (FamilyOrdering f)) *
    ∏ i, gaussianCoefficient τ σ (f i)) = _
  rw [hO,hProd,offspringAmplitude,hCard,ite_eq_right (Nat.ne_of_gt m.property.1),hermiteLinearCoeff]
  field_simp

end LovaszTheta.Circulant.EvenTreeType
