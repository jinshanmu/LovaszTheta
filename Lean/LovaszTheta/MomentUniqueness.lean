module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Analytic.Order

/-!
# Uniqueness from moments with exponential integrability

The complex moment-generating functions are entire. Their
derivatives at zero are the power moments, so equality of moments
implies equality of the measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace LovaszTheta.Circulant

/-- Finite real measures with all exponential moments are determined
by their power moments. -/
theorem measure_eq_of_exponential_moments {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : integrableExpSet id μ = univ) (hν : integrableExpSet id ν = univ)
    (h : ∀ j : ℕ, (∫ x, x^j ∂μ) = ∫ x, x^j ∂ν) : μ = ν := by
  let F := complexMGF id μ
  let G := complexMGF id ν
  have hF : AnalyticOnNhd ℂ F univ := by
    intro z _
    exact analyticAt_complexMGF (by rw [hμ, interior_univ]; exact mem_univ _)
  have hG : AnalyticOnNhd ℂ G univ := by
    intro z _
    exact analyticAt_complexMGF (by rw [hν, interior_univ]; exact mem_univ _)
  have hμ₀ : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simp [hμ]
  have hν₀ : (0 : ℂ).re ∈ interior (integrableExpSet id ν) := by simp [hν]
  have hD (j : ℕ) : iteratedDeriv j F 0 = iteratedDeriv j G 0 := by
    unfold F G
    rw [iteratedDeriv_complexMGF hμ₀, iteratedDeriv_complexMGF hν₀]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
      integral_complex_ofReal, h j]
  have hA : AnalyticAt ℂ (F-G) 0 := (hF 0 (mem_univ _)).sub (hG 0 (mem_univ _))
  have hZ (j : ℕ) : iteratedDeriv j (F-G) 0 = 0 := by
    rw [iteratedDeriv_sub ((hF 0 (mem_univ _)).contDiffAt) ((hG 0 (mem_univ _)).contDiffAt), hD, sub_self]
  have hTop : analyticOrderAt (F-G) 0 = ⊤ := by
    cases he : analyticOrderAt (F-G) 0 with
    | top => rfl
    | coe j =>
      have hn := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hA).mp he).2
      exact (hn (hZ j)).elim
  have hLoc : F =ᶠ[𝓝 (0 : ℂ)] G := by
    filter_upwards [analyticOrderAt_eq_top.mp hTop] with z hz
    exact sub_eq_zero.mp hz
  exact Measure.ext_of_complexMGF_id_eq (hF.eq_of_eventuallyEq hG hLoc)

end LovaszTheta.Circulant
