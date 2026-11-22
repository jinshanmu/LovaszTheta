module

public import LovaszTheta.HermiteCalculus
public import LovaszTheta.GaussianCoordinates
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Data.Finsupp.Multiset

/-!
# Hermite products on Gaussian coordinates

The product Gaussian measure has the prescribed standard Gaussian
law on every finite set of coordinates. The finite products of
Hermite functions consequently form an orthonormal family in L².
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace NNReal ENNReal

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- Independent standard normal coordinates, indexed by any type. -/
noncomputable abbrev gaussianProduct (I : Type*) : Measure (I → ℝ) :=
  Measure.infinitePi (fun _ : I ↦ gaussianReal 0 1)

lemma gaussianProduct_restrict (s : Finset I) :
    MeasurePreserving s.restrict (gaussianProduct I) (gaussianCoordinates s) :=
  ⟨measurable_restrict s,Measure.infinitePi_map_restrict _⟩

private lemma prod_restrict_eq (s : Finset I) (f : I → ℝ → ℝ) (x : I → ℝ) :
    (∏ i : s, f i.val (s.restrict x i)) = ∏ i ∈ s, f i (x i) :=
  prod_coe_sort s (fun i ↦ f i (x i))

lemma integral_gaussianProduct_prod (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    (∫ x : I → ℝ, ∏ i ∈ s, f i (x i) ∂gaussianProduct I) =
      ∏ i ∈ s, ∫ y, f i y ∂gaussianReal 0 1 := by
  simp only [← prod_restrict_eq s f]
  let g (x : s → ℝ) := ∏ i : s, f i.val (x i)
  change (∫ x, g (s.restrict x) ∂gaussianProduct I) = _
  have hg : Measurable g :=
    Finset.measurable_prod _ (fun i _ ↦ (hf i.val i.property).comp (measurable_pi_apply i))
  rw [← integral_map (measurable_restrict s).aemeasurable hg.aestronglyMeasurable,
    (gaussianProduct_restrict s).map_eq]
  exact (integral_fintype_prod_eq_prod (fun i : s ↦ f i.val)).trans
    (prod_coe_sort s (fun i ↦ ∫ y, f i y ∂gaussianReal 0 1))

lemma integrable_gaussianProduct_prod (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (gaussianReal 0 1)) :
    Integrable (fun x : I → ℝ ↦ ∏ i ∈ s, f i (x i)) (gaussianProduct I) := by
  simp only [← prod_restrict_eq s f]
  exact (gaussianProduct_restrict s).integrable_comp_of_integrable
    (Integrable.fintype_prod (fun i : s ↦ hf i.val i.property))

/-- The multivariate Hermite product with finitely supported multiplicities. -/
noncomputable def hermiteProduct (m : I →₀ ℕ) (x : I → ℝ) : ℝ :=
  ∏ i ∈ m.support, normalizedHermite (m i) (x i)

lemma hermiteProduct_eq_prod_of_support_subset (m : I →₀ ℕ) {s : Finset I} (hm : m.support ⊆ s) (x : I → ℝ) :
    hermiteProduct m x = ∏ i ∈ s, normalizedHermite (m i) (x i) := by
  unfold hermiteProduct
  exact prod_subset hm fun i _ hi ↦ by simp [Finsupp.notMem_support_iff.mp hi,normalizedHermite]

lemma continuous_normalizedHermite (j : ℕ) : Continuous (normalizedHermite j) := by
  unfold normalizedHermite
  fun_prop

lemma measurable_hermiteProduct (m : I →₀ ℕ) : Measurable (hermiteProduct m) :=
  Finset.measurable_prod _ (fun i _ ↦ (continuous_normalizedHermite (m i)).measurable.comp (measurable_pi_apply i))

lemma integrable_normalizedHermite_mul (a b : ℕ) :
    Integrable (fun x ↦ normalizedHermite a x * normalizedHermite b x) (gaussianReal 0 1) := by
  have h : ∀ j : ℕ, HasPolynomialGrowth (normalizedHermite j) := fun j ↦ by
    have he : normalizedHermite j = (realHermite j * Polynomial.C ((Real.sqrt j.factorial)⁻¹)).eval := by
      funext x
      simp [normalizedHermite,div_eq_mul_inv]
    rw [he]
    exact HasPolynomialGrowth.eval_polynomial _
  exact ((h a).mul (h b)).integrable_gaussian
    ((continuous_normalizedHermite a).mul (continuous_normalizedHermite b)) 1

lemma memLp_hermiteProduct (m : I →₀ ℕ) : MemLp (hermiteProduct m) 2 (gaussianProduct I) := by
  rw [memLp_two_iff_integrable_sq (measurable_hermiteProduct m).aestronglyMeasurable]
  simp only [hermiteProduct, pow_two, ← prod_mul_distrib]
  exact integrable_gaussianProduct_prod _ _ fun i _ ↦ integrable_normalizedHermite_mul (m i) (m i)

/-- The Hermite product as an element of Gaussian L². -/
noncomputable def hermiteProductL2 (m : I →₀ ℕ) : Lp ℝ 2 (gaussianProduct I) :=
  (memLp_hermiteProduct m).toLp (hermiteProduct m)

lemma hermiteProductL2_ae_eq (m : I →₀ ℕ) :
    hermiteProductL2 m =ᵐ[gaussianProduct I] hermiteProduct m :=
  (memLp_hermiteProduct m).coeFn_toLp

theorem orthonormal_hermiteProductL2 : Orthonormal ℝ (hermiteProductL2 (I := I)) := by
  rw [orthonormal_iff_ite]
  intro m q
  let s := m.support ∪ q.support
  have hm : m.support ⊆ s := subset_union_left
  have hq : q.support ⊆ s := subset_union_right
  have he : ⟪hermiteProductL2 m, hermiteProductL2 q⟫ =
      ∫ x, ∏ i ∈ s, normalizedHermite (m i) (x i)*normalizedHermite (q i) (x i) ∂gaussianProduct I := by
    rw [MeasureTheory.L2.inner_def]
    exact integral_congr_ae (((hermiteProductL2_ae_eq m).and (hermiteProductL2_ae_eq q)).mono fun x h ↦ by
      simp only [RCLike.inner_apply, RCLike.conj_to_real,h.1,h.2,mul_comm,
        hermiteProduct_eq_prod_of_support_subset m hm,hermiteProduct_eq_prod_of_support_subset q hq]
      rw [← prod_mul_distrib])
  rw [he,integral_gaussianProduct_prod s (fun i x ↦ normalizedHermite (m i) x * normalizedHermite (q i) x)
    (fun i _ ↦ ((continuous_normalizedHermite (m i)).mul (continuous_normalizedHermite (q i))).measurable)]
  simp_rw [integral_normalizedHermite_mul]
  by_cases hm : m = q
  · simp [hm]
  · rw [ite_eq_right hm]
    obtain ⟨i,hi⟩ : ∃ i, m i ≠ q i := by
      by_contra h
      apply hm
      exact Finsupp.ext (by push Not at h; exact h)
    have his : i ∈ s := by
      simp only [s, mem_union, Finsupp.mem_support_iff]
      by_contra h
      push Not at h
      exact hi (h.1.trans h.2.symm)
    exact prod_eq_zero his (ite_eq_right hi)

end LovaszTheta.Circulant
