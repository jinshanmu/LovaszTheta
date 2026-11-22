module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Independent Gaussian counterparts of the tree coordinates

A finite product of standard normals is the standard Gaussian in
the Euclidean coordinate space. Its linear forms have variance
equal to the squared coefficient norm.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace LovaszTheta.Circulant

variable {I : Type*} [Fintype I]

/-- Independent standard normal coordinates for a finite family. -/
noncomputable abbrev gaussianCoordinates (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ ↦ gaussianReal 0 1)

lemma measurable_coordinate_sum (a : I → ℝ) : Measurable (fun x : I → ℝ ↦ ∑ i, a i*x i) := by
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable (fun x : I → ℝ ↦ x i) := measurable_pi_apply i
  have ha : Measurable (fun _ : I → ℝ ↦ a i) := measurable_const
  exact ha.mul hi

/-- The linear combination of independent Gaussian coordinates has the
centered Gaussian law with its squared coefficient norm as variance. -/
theorem map_gaussianCoordinates_sum (a : I → ℝ) :
    (gaussianCoordinates I).map (fun x ↦ ∑ i, a i*x i) =
      gaussianReal 0 (∑ i, a i^2).toNNReal := by
  let u : EuclideanSpace ℝ I := WithLp.toLp 2 a
  let L : StrongDual ℝ (EuclideanSpace ℝ I) := innerSL ℝ u
  have hL (x : I → ℝ) : L (WithLp.toLp 2 x) = ∑ i, a i*x i := by
    simp [L, u, innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  calc
    _ = (stdGaussian (EuclideanSpace ℝ I)).map L := by
      rw [← map_pi_eq_stdGaussian, Measure.map_map L.continuous.measurable (by fun_prop)]
      congr 1
      funext x
      exact (hL x).symm
    _ = _ := by
      rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
      change gaussianReal 0 (‖innerSL ℝ u‖^2).toNNReal = _
      rw [innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]

theorem integral_test_gaussianCoordinates_sum (a : I → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ x, f (∑ i, a i*x i) ∂gaussianCoordinates I) =
      ∫ g, f g ∂gaussianReal 0 (∑ i, a i^2).toNNReal := by
  rw [← map_gaussianCoordinates_sum a]
  exact (integral_map (measurable_coordinate_sum a).aemeasurable hf.aestronglyMeasurable).symm

end LovaszTheta.Circulant
