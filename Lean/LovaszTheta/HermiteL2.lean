module

public import LovaszTheta.HermiteMoments
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hermite functions in Gaussian L²

The normalized functions are orthonormal in the Gaussian Hilbert
space. The leading coefficient of a Hermite polynomial is one,
so vanishing Hermite coefficients imply vanishing power moments.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Polynomial
open scoped Polynomial RealInnerProductSpace ENNReal

namespace LovaszTheta.Circulant

lemma memLp_gaussian_eval_two (v : NNReal) (p : ℝ[X]) :
    MemLp p.eval 2 (gaussianReal 0 v) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have h := integrable_gaussian_eval v (p^2)
  change Integrable (fun x ↦ (p^2).eval x) (gaussianReal 0 v) at h
  simpa only [eval_pow] using h

lemma memLp_gaussian_pow_two (v : NNReal) (j : ℕ) :
    MemLp (fun x : ℝ ↦ x^j) 2 (gaussianReal 0 v) := by
  simpa only [eval_pow, eval_X] using memLp_gaussian_eval_two v ((X : ℝ[X])^j)

lemma memLp_normalizedHermite (j : ℕ) :
    MemLp (normalizedHermite j) 2 (gaussianReal 0 1) := by
  change MemLp (fun x ↦ (realHermite j).eval x / Real.sqrt j.factorial) 2 (gaussianReal 0 1)
  simpa only [eval_mul, eval_C, div_eq_inv_mul] using
    memLp_gaussian_eval_two 1 (C (Real.sqrt j.factorial)⁻¹ * realHermite j)

/-- The normalized Hermite function as a vector of the Gaussian Hilbert space. -/
noncomputable def hermiteL2 (j : ℕ) : Lp ℝ 2 (gaussianReal 0 1) :=
  (memLp_normalizedHermite j).toLp (normalizedHermite j)

lemma hermiteL2_ae_eq (j : ℕ) : hermiteL2 j =ᵐ[gaussianReal 0 1] normalizedHermite j :=
  (memLp_normalizedHermite j).coeFn_toLp

/-- The Hermite functions give an orthonormal family in Gaussian L². -/
theorem orthonormal_hermiteL2 : Orthonormal ℝ hermiteL2 := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [MeasureTheory.L2.inner_def]
  exact (integral_congr_ae ((hermiteL2_ae_eq i).and (hermiteL2_ae_eq j) |>.mono
    fun x hx ↦ by simp only [hx.1, hx.2, RCLike.inner_apply, RCLike.conj_to_real, mul_comm])).trans
      (integral_normalizedHermite_mul i j)

lemma realHermite_monic (j : ℕ) : (realHermite j).Monic :=
  (Polynomial.hermite_monic j).map (Int.castRingHom ℝ)

lemma realHermite_natDegree (j : ℕ) : (realHermite j).natDegree = j := by
  rw [realHermite, (Polynomial.hermite_monic j).natDegree_map, Polynomial.natDegree_hermite]

private lemma eval_realHermite_split (j : ℕ) (x : ℝ) :
    (realHermite j).eval x = (∑ k ∈ range j, (realHermite j).coeff k*x^k)+x^j := by
  rw [Polynomial.eval_eq_sum_range, realHermite_natDegree, sum_range_succ]
  have h : (realHermite j).coeff j = 1 := by
    have h := (realHermite_monic j).coeff_natDegree
    rwa [realHermite_natDegree j] at h
  rw [h, one_mul]

/-- Orthogonality to the Hermite polynomials implies vanishing moments
against the monomials, by their triangular change of basis. -/
theorem integral_mul_pow_eq_zero_of_hermite (f : ℝ → ℝ)
    (hf : MemLp f 2 (gaussianReal 0 1))
    (h : ∀ j, (∫ x, f x*(realHermite j).eval x ∂gaussianReal 0 1) = 0) (n : ℕ) :
    (∫ x, f x*x^n ∂gaussianReal 0 1) = 0 := by
  induction n using Nat.strong_induction_on with
  | ind j ih =>
    have hI (k : ℕ) : Integrable (fun x ↦ f x*x^k) (gaussianReal 0 1) :=
      hf.integrable_mul (memLp_gaussian_pow_two 1 k)
    let p := realHermite j
    have hpoly (x : ℝ) :
        f x*p.eval x = (∑ k ∈ range j, p.coeff k*(f x*x^k))+f x*x^j := by
      rw [eval_realHermite_split, mul_add, mul_sum]
      congr 1
      exact sum_congr rfl fun k _ ↦ by ring
    have hs := h j
    change (∫ x, f x*p.eval x ∂gaussianReal 0 1) = 0 at hs
    simp_rw [hpoly] at hs
    rw [integral_add (integrable_finsetSum _ fun k _ ↦ (hI k).const_mul _) (hI j),
      integral_finsetSum _ fun k _ ↦ (hI k).const_mul _] at hs
    simp_rw [integral_const_mul] at hs
    have he : (∑ k ∈ range j, p.coeff k*∫ x, f x*x^k ∂gaussianReal 0 1) = 0 :=
      sum_eq_zero fun k hk ↦ by rw [ih k (mem_range.mp hk), mul_zero]
    simpa only [he, zero_add] using hs

end LovaszTheta.Circulant
