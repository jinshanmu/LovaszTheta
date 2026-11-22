module

public import LovaszTheta.GaussianTruncation
public import LovaszTheta.HermiteGenerating

/-!
# Hermite polynomials of the infinite Gaussian series

Apply the finite generating-function identity to normalized
truncations. The Gaussian higher moments give convergence of
the Hermite polynomials in L², preserving each product coefficient.
-/

@[expose] public section

open Finset Filter MeasureTheory Polynomial
open scoped Classical ENNReal Topology RealInnerProductSpace Polynomial

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- The element of Gaussian L² obtained by applying a normalized
Hermite polynomial to a Gaussian series. -/
noncomputable def gaussianHermiteL2 (j : ℕ) (a : lp (fun _ : I ↦ ℝ) 2) :
    Lp ℝ 2 (gaussianProduct I) :=
  (exists_continuous_gaussianPolynomial (I := I) (realHermite j * C ((Real.sqrt j.factorial)⁻¹))).choose a

lemma continuous_gaussianHermiteL2 (j : ℕ) : Continuous (gaussianHermiteL2 (I := I) j) :=
  (exists_continuous_gaussianPolynomial _).choose_spec.1

lemma gaussianHermiteL2_ae_eq (j : ℕ) (a : lp (fun _ : I ↦ ℝ) 2) :
    gaussianHermiteL2 j a =ᵐ[gaussianProduct I] fun x ↦ normalizedHermite j (gaussianSeries I a x) := by
  exact ((exists_continuous_gaussianPolynomial (I := I)
    (realHermite j*C (Real.sqrt j.factorial)⁻¹)).choose_spec.2 a).mono fun x hx ↦ by
      simp only [gaussianHermiteL2,hx,eval_mul,eval_C,normalizedHermite,div_eq_mul_inv]

/-- The finite Hermite identity as an equality in L². -/
theorem gaussianHermiteL2_finite (j : ℕ) (s : Finset I) (a : lp (fun _ : I ↦ ℝ) 2)
    (ha : ‖a‖ = 1) (hSupport : ∀ i ∉ s, a i = 0) :
    gaussianHermiteL2 j a = ∑ m ∈ finsuppAntidiag s j, hermiteLinearCoeff a m • hermiteProductL2 m := by
  have hEval : gaussianSeries I a =ᵐ[gaussianProduct I] fun x ↦ ∑ i ∈ s, a i*x i := by
    have h := gaussianSeries_finsetSum_ae s a
    rwa [show (∑ i ∈ s, lp.single 2 i (a i)) = a from truncateCoefficients_eq_self hSupport] at h
  have hVar : ∑ i ∈ s, (a i)^2 = 1 := by rw [sum_sq_eq_gaussianCoefficient_norm_sq hSupport,ha,one_pow]
  apply Lp.ext
  refine (gaussianHermiteL2_ae_eq j a).trans ?_
  refine .trans ?_ (Lp.coeFn_finsetSum _ _).symm
  have hTerms (m : I →₀ ℕ) : (hermiteLinearCoeff a m • hermiteProductL2 m : Lp ℝ 2 (gaussianProduct I)) =ᵐ[gaussianProduct I]
      fun x ↦ hermiteLinearCoeff a m * hermiteProduct m x :=
    (Lp.coeFn_smul _ _).trans ((hermiteProductL2_ae_eq m).mono fun x hx ↦ by simp only [Pi.smul_apply,smul_eq_mul,hx])
  refine .trans ?_ (eventuallyEq_sum fun m _ ↦ hTerms m).symm
  exact hEval.mono fun x hx ↦ by
    simp only [Finset.sum_apply,hx,normalizedHermite_linearCombination_finsupp s a x hVar j]

/-- The polynomial of degree j lies in the closed span of the Hermite
products with total degree j, and hence in every larger such span. -/
theorem gaussianHermiteL2_mem_closedSpan (j : ℕ) (a : lp (fun _ : I ↦ ℝ) 2) (ha : ‖a‖ = 1)
    (P : (I →₀ ℕ) → Prop) (hP : ∀ m, m.toMultiset.card = j → P m) :
    gaussianHermiteL2 j a ∈
      (Submodule.span ℝ (Set.range (fun m : {m : I →₀ ℕ // P m} ↦ hermiteProductL2 m.val))).topologicalClosure := by
  let S := Submodule.span ℝ (Set.range (fun m : {m : I →₀ ℕ // P m} ↦ hermiteProductL2 m.val))
  have hLim := (continuous_gaussianHermiteL2 (I := I) j).continuousAt.tendsto.comp (tendsto_normalizedTruncation a ha)
  apply (Submodule.isClosed_topologicalClosure S).mem_of_tendsto hLim
  filter_upwards [eventually_normalizedTruncation_norm_one a ha] with s hs
  change gaussianHermiteL2 j (normalizedTruncation a s) ∈ S.topologicalClosure
  rw [gaussianHermiteL2_finite j s _ hs (normalizedTruncation_apply_of_notMem a s)]
  apply S.le_topologicalClosure
  apply Submodule.sum_mem
  intro m hm
  have hCard : m.toMultiset.card = j := by
    rw [Finsupp.card_toMultiset]
    exact (mem_finsuppAntidiag'.mp hm).1
  exact Submodule.smul_mem S _ (Submodule.subset_span ⟨⟨m,hP m hCard⟩,rfl⟩)

lemma continuous_hermiteLinearCoeff (m : I →₀ ℕ) :
    Continuous (fun a : lp (fun _ : I ↦ ℝ) 2 ↦ hermiteLinearCoeff a m) := by
  unfold hermiteLinearCoeff
  have hc (i : I) : Continuous (fun a : lp (fun _ : I ↦ ℝ) 2 ↦ a i) :=
    (continuous_apply i).comp (lp.uniformContinuous_coe (p := 2)).continuous
  exact continuous_const.mul (continuous_finsetProd _ fun i _ ↦ (hc i).pow _)

private lemma inner_gaussianHermiteL2_finite (j : ℕ) (s : Finset I) (a : lp (fun _ : I ↦ ℝ) 2)
    (ha : ‖a‖ = 1) (hSupport : ∀ i ∉ s, a i = 0) (m : I →₀ ℕ) :
    ⟪gaussianHermiteL2 j a,hermiteProductL2 m⟫ =
      if m ∈ finsuppAntidiag s j then hermiteLinearCoeff a m else 0 := by
  rw [gaussianHermiteL2_finite j s a ha hSupport,sum_inner]
  simp only [real_inner_smul_left,orthonormal_iff_ite.mp orthonormal_hermiteProductL2,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']

/-- Each coefficient survives passage to the square-summable
Gaussian series with its multinomial value. -/
theorem inner_gaussianHermiteL2 (j : ℕ) (a : lp (fun _ : I ↦ ℝ) 2)
    (ha : ‖a‖ = 1) (m : I →₀ ℕ) :
    ⟪gaussianHermiteL2 j a,hermiteProductL2 m⟫ =
      if m.toMultiset.card = j then hermiteLinearCoeff a m else 0 := by
  have hLeft : Tendsto (fun s : Finset I ↦ ⟪gaussianHermiteL2 j (normalizedTruncation a s),hermiteProductL2 m⟫)
      atTop (𝓝 ⟪gaussianHermiteL2 j a,hermiteProductL2 m⟫) :=
    (((continuous_gaussianHermiteL2 j).inner continuous_const).continuousAt.tendsto.comp
      (tendsto_normalizedTruncation a ha))
  have hRightCont : Continuous (fun u : lp (fun _ : I ↦ ℝ) 2 ↦
      if m.toMultiset.card = j then hermiteLinearCoeff u m else 0) := by
    split_ifs
    · exact continuous_hermiteLinearCoeff m
    · exact continuous_const
  refine tendsto_nhds_unique hLeft ((hRightCont.continuousAt.tendsto.comp
    (tendsto_normalizedTruncation a ha)).congr' ?_)
  filter_upwards [eventually_normalizedTruncation_norm_one a ha,eventually_ge_atTop m.support] with s hs hm
  rw [Function.comp_apply,inner_gaussianHermiteL2_finite j s _ hs (normalizedTruncation_apply_of_notMem a s)]
  have hMem : m ∈ s.finsuppAntidiag j ↔ m.toMultiset.card = j := by
    rw [mem_finsuppAntidiag',Finsupp.card_toMultiset,and_iff_left hm]
    rfl
  by_cases he : m.toMultiset.card = j
  · rw [ite_eq_left he,ite_eq_left (hMem.mpr he)]
  · rw [ite_eq_right he,ite_eq_right (mt hMem.mp he)]

end LovaszTheta.Circulant
