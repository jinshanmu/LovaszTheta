module

public import LovaszTheta.GaussianActivationSeries
public import LovaszTheta.GaussianBranchingRecursion

/-!
# The Gaussian fixed-point equation

The centered activation has the Hermite coefficient prescribed
by the branching recursion at each nonleaf type. Grafting
places these coefficients on the Gaussian coordinates. The
remaining coefficient is two on the leaf.
-/

@[expose] public section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace ENNReal

namespace LovaszTheta.Circulant.EvenTreeType

/-- The centered activation with its membership in the domain of grafting. -/
noncomputable def activationInEvenSpan {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ)
    (a : lp (fun _ : EvenTreeType ↦ ℝ) 2) (ha : ‖a‖ = 1) :
    evenHermiteSeries.toLinearMap.range :=
  ⟨centeredGaussianActivation hτ σ a ha,evenHermiteSeries_range.symm ▸
    centeredGaussianActivation_mem_even_span hτ σ a ha⟩

/-- The coefficient vector from the branching law solves the Gaussian fixed-point equation. -/
theorem gaussian_equation {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hσ' : σ ≤ Real.sqrt (2*Real.pi)) (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    let u := gaussianCoefficientVector hτ hσ hσ' hMean
    let C := activationInEvenSpan hτ.le σ u (norm_gaussianCoefficientVector hτ hσ hσ' hMean)
    σ • gaussianSeries EvenTreeType u = (2 : ℝ) • gaussianCoordinateL2 leaf + gaussianGraftIsometry C := by
  let u := gaussianCoefficientVector hτ hσ hσ' hMean
  let C := activationInEvenSpan hτ.le σ u (norm_gaussianCoefficientVector hτ hσ hσ' hMean)
  let b := evenHermiteSeries.equivRange.symm C
  have hC : evenHermiteSeries b = C.val :=
    congrArg Subtype.val (evenHermiteSeries.equivRange.apply_symm_apply C)
  have hC' : gaussianGraftIsometry C = graftedSeries b := by
    have h := gaussianGraftIsometry_series b
    rw [evenHermiteSeries.equivRange.apply_symm_apply C] at h
    exact h
  have hCoeff (m : PositiveEvenHermiteIndex EvenTreeType) : b m = σ*u (graftOfIndex m) := by
    calc
      _ = ⟪evenHermiteSeries b,hermiteProductL2 m.val⟫ :=
        (inner_orthonormalSeries (orthonormal_hermiteProductL2.comp _ Subtype.val_injective) b m).symm
      _ = activationCoefficient τ σ m.val.toMultiset.card * hermiteLinearCoeff u m.val := by
        rw [hC]
        exact inner_centeredGaussianActivation hτ.le σ u (norm_gaussianCoefficientVector hτ hσ hσ' hMean) m
      _ = _ := (gaussianCoefficient_graftOfIndex τ σ hσ.ne' m).symm
  have hU : HasSum (fun T : EvenTreeType ↦ (σ*u T) • gaussianCoordinateL2 T)
      (σ • gaussianSeries EvenTreeType u) := by
    simpa only [smul_smul,gaussianSeries] using (hasSum_orthonormalSeries orthonormal_gaussianCoordinateL2 u).const_smul σ
  have hLeaf : σ*u leaf = 2 := by
    change σ*gaussianCoefficient τ σ leaf = _
    rw [gaussianCoefficient_leaf]
    field_simp
  have hG : graftedSeries b =
      ∑' T : {T : EvenTreeType // T ≠ leaf}, (σ*u T.val) • gaussianCoordinateL2 T.val := by
    have h := hasSum_orthonormalSeries (orthonormal_gaussianCoordinateL2.comp _ graftOfIndex_injective) b
    change HasSum (fun m ↦ b m • gaussianCoordinateL2 (graftOfIndex m)) (graftedSeries b) at h
    simp only [hCoeff] at h
    exact h.tsum_eq.symm.trans (graftOfIndexEquiv.tsum_eq
      (fun T ↦ (σ*u T.val) • gaussianCoordinateL2 T.val))
  change (σ : ℝ) • gaussianSeries EvenTreeType u = (2 : ℝ) • gaussianCoordinateL2 leaf + gaussianGraftIsometry C
  rw [hC',hG,← hU.tsum_eq]
  have h := hU.summable.sum_add_tsum_compl (s := {leaf})
  simp only [sum_singleton,hLeaf] at h
  let e : {T : EvenTreeType // T ≠ leaf} ≃ ↑((↑({leaf} : Finset EvenTreeType) : Set EvenTreeType)ᶜ) :=
    (Equiv.refl _).subtypeEquiv (fun T ↦ by simp)
  exact h.symm.trans (congrArg ((2 : ℝ) • gaussianCoordinateL2 leaf + ·)
    (e.tsum_eq (fun T ↦ (σ*u T.val) • gaussianCoordinateL2 T.val)).symm)

end LovaszTheta.Circulant.EvenTreeType
