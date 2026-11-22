module

public import LovaszTheta.HermiteProducts
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Finite Hermite expansion of a linear form

The generating function factors over the coordinates of a unit
vector. Multinomial Leibniz gives the Hermite coefficients by
differentiating at zero.
-/

@[expose] public section

open Finset Polynomial
open scoped Classical Nat ContDiff Polynomial

namespace LovaszTheta.Circulant

/-- The probabilists' Hermite generating function. -/
noncomputable def hermiteGenerating (x t : ℝ) : ℝ := Real.exp (t*x-t^2/2)

lemma contDiff_hermiteGenerating (x : ℝ) : ContDiff ℝ ∞ (hermiteGenerating x) := by
  unfold hermiteGenerating
  fun_prop

lemma iteratedDeriv_hermiteGenerating (j : ℕ) (x : ℝ) :
    iteratedDeriv j (hermiteGenerating x) 0 = (realHermite j).eval x := by
  let G (y : ℝ) := Real.exp (-(y^2/2))
  have he : hermiteGenerating x = fun t ↦ Real.exp (x^2/2)*G (x-t) := by
    funext t
    unfold hermiteGenerating G
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_sub]
  change Real.exp (x^2/2) * ((-1 : ℝ)^j * iteratedDeriv j G (x-0)) = _
  rw [sub_zero, iteratedDeriv_eq_iterate, mul_comm (Real.exp (x^2/2)), ← Polynomial.hermite_eq_deriv_gaussian']
  simp only [realHermite, Polynomial.eval_map, Polynomial.aeval_def]
  rfl

private lemma iteratedDeriv_hermiteGenerating_scale (j : ℕ) (x u : ℝ) :
    iteratedDeriv j (fun t ↦ hermiteGenerating x (u*t)) 0 = u^j * (realHermite j).eval x := by
  have he := congrFun (iteratedDeriv_comp_const_mul (n := j) ((contDiff_hermiteGenerating x).of_le (by simp)) u) 0
  simpa only [mul_zero, iteratedDeriv_hermiteGenerating] using he

private lemma iteratedDeriv_prod_multinomial {I : Type*} (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (∏ i ∈ s, f i) x =
      ∑ m ∈ piAntidiag s j, (Nat.multinomial s m : ℝ) * ∏ i ∈ s, iteratedDeriv (m i) (f i) x := by
  induction s using Finset.cons_induction generalizing j with
  | empty =>
    cases j with
    | zero => simp
    | succ j =>
      rw [piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero _)]
      change iteratedDeriv (j+1) (fun _ : ℝ ↦ (1 : ℝ)) x = ∑ m ∈ ∅, _
      simp [iteratedDeriv_const]
  | cons a s ha ih =>
    have hC (k : ℕ) : ContDiffAt ℝ k (∏ i ∈ s, f i) x :=
      ((contDiff_prod' (t := s) fun i _ ↦ hf i).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    have hCA : ContDiffAt ℝ j (f a) x := ((hf a).of_le (by simp)).contDiffAt
    rw [prod_cons, iteratedDeriv_mul hCA (hC j), ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun aDegree restDegree ↦ (j.choose aDegree : ℝ) * iteratedDeriv aDegree (f a) x *
        iteratedDeriv restDegree (∏ i ∈ s, f i) x)]
    simp only [piAntidiag_cons, sum_disjiUnion, sum_map, addRightEmbedding_apply]
    apply sum_congr rfl
    intro p hp
    rw [ih, mul_sum]
    apply sum_congr rfl
    intro m hm
    obtain ⟨hSum,hZero⟩ := mem_piAntidiag.mp hm
    let g := m + fun i ↦ if i = a then p.1 else 0
    have hA : g a = p.1 := by simp [g,not_not.mp (mt (hZero a) ha)]
    have hS (i : I) (hi : i ∈ s) : g i = m i := by
      simp [g, ne_of_mem_of_not_mem hi ha]
    have hNat : Nat.multinomial (s.cons a ha) g = j.choose p.1 * Nat.multinomial s m := by
      rw [Nat.multinomial_cons, hA, sum_congr rfl hS, hSum, mem_antidiagonal.mp hp,
        Nat.multinomial_congr hS]
    change _ = (Nat.multinomial (s.cons a ha) g : ℝ) * ∏ i ∈ s.cons a ha, iteratedDeriv (g i) (f i) x
    have hProd : (∏ i ∈ s, iteratedDeriv (g i) (f i) x) = ∏ i ∈ s, iteratedDeriv (m i) (f i) x :=
      prod_congr rfl (fun i hi ↦ by rw [hS i hi])
    rw [hNat, Nat.cast_mul, prod_cons, hA, hProd]
    ring

/-- The finite generating-function identity for a unit vector. -/
theorem realHermite_linearCombination {I : Type*} (s : Finset I) (u x : I → ℝ)
    (hu : ∑ i ∈ s, u i^2 = 1) (j : ℕ) :
    (realHermite j).eval (∑ i ∈ s, u i*x i) =
      ∑ m ∈ piAntidiag s j,
        (Nat.multinomial s m : ℝ) * ∏ i ∈ s, u i^(m i) * (realHermite (m i)).eval (x i) := by
  let f (i : I) (t : ℝ) := hermiteGenerating (x i) (u i*t)
  have hF : hermiteGenerating (∑ i ∈ s, u i*x i) = ∏ i ∈ s, f i := by
    funext t
    simp only [Finset.prod_apply, f, hermiteGenerating, ← Real.exp_sum]
    congr 1
    simp only [mul_pow, sum_sub_distrib, ← sum_div, ← sum_mul, hu, one_mul, mul_sum]
    congr 1
    exact sum_congr rfl fun i _ ↦ by ring
  rw [← iteratedDeriv_hermiteGenerating, hF]
  have hC (i : I) : ContDiff ℝ ∞ (f i) :=
    (contDiff_hermiteGenerating (x i)).comp (by fun_prop : ContDiff ℝ ∞ fun t ↦ u i*t)
  rw [iteratedDeriv_prod_multinomial s f hC]
  simp_rw [f, iteratedDeriv_hermiteGenerating_scale]

private lemma multinomial_normalize {I : Type*} (s : Finset I) (m : I → ℕ) :
    (Nat.multinomial s m : ℝ) * ∏ i ∈ s, Real.sqrt (m i).factorial =
      Real.sqrt (Nat.multinomial s m) * Real.sqrt ((∑ i ∈ s, m i)!).cast := by
  have h : (∏ i ∈ s, ((m i)! : ℝ)) * (Nat.multinomial s m : ℝ) = ((∑ i ∈ s, m i)! : ℝ) := by
    exact_mod_cast Nat.multinomial_spec s m
  rw [← h, Real.sqrt_mul (by positivity)]
  have hS : Real.sqrt (∏ i ∈ s, ((m i)! : ℝ)) = ∏ i ∈ s, Real.sqrt (m i).factorial :=
    Real.sqrt_prod _ (fun _ _ ↦ by positivity)
  rw [hS]
  have hM := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ Nat.multinomial s m)
  calc
    _ = (Real.sqrt (Nat.multinomial s m)*Real.sqrt (Nat.multinomial s m)) *
        ∏ i ∈ s, Real.sqrt (m i).factorial := by rw [hM]
    _ = _ := by ring

/-- The normalized expansion has the square root of the
multinomial coefficient for each Hermite product. -/
theorem normalizedHermite_linearCombination {I : Type*} (s : Finset I) (u x : I → ℝ)
    (hu : ∑ i ∈ s, u i^2 = 1) (j : ℕ) :
    normalizedHermite j (∑ i ∈ s, u i*x i) =
      ∑ m ∈ piAntidiag s j,
        Real.sqrt (Nat.multinomial s m) * ∏ i ∈ s, u i^(m i)*normalizedHermite (m i) (x i) := by
  rw [normalizedHermite, realHermite_linearCombination s u x hu, sum_div]
  apply sum_congr rfl
  intro m hm
  have hSum := (mem_piAntidiag.mp hm).1
  have hNorm := multinomial_normalize s m
  rw [hSum] at hNorm
  have h (i : I) : (realHermite (m i)).eval (x i) =
      normalizedHermite (m i) (x i) * Real.sqrt (m i).factorial := by
    rw [normalizedHermite, div_mul_cancel₀ _ (by positivity)]
  simp only [h]
  simp_rw [← mul_assoc (u _ ^ _), Finset.prod_mul_distrib]
  rw [mul_left_comm, hNorm, mul_comm (Real.sqrt (Nat.multinomial s m)), mul_assoc]
  apply (div_eq_iff (by positivity : Real.sqrt j.factorial ≠ 0)).mpr
  ring

/-- The coefficient of a Hermite product in the generating-function identity. -/
noncomputable def hermiteLinearCoeff {I : Type*} (u : I → ℝ) (m : I →₀ ℕ) : ℝ :=
  Real.sqrt m.multinomial * ∏ i ∈ m.support, u i^(m i)

/-- The finite expansion indexed by the supported multiplicities. -/
theorem normalizedHermite_linearCombination_finsupp {I : Type*} (s : Finset I) (u x : I → ℝ)
    (hu : ∑ i ∈ s, u i^2 = 1) (j : ℕ) :
    normalizedHermite j (∑ i ∈ s, u i*x i) =
      ∑ m ∈ finsuppAntidiag s j, hermiteLinearCoeff u m * hermiteProduct m x := by
  rw [normalizedHermite_linearCombination s u x hu, finsuppAntidiag, sum_map]
  conv_lhs => rw [← sum_attach]
  apply sum_congr rfl
  intro a _
  let m : I →₀ ℕ := ⟨s.filter (fun i ↦ a.val i ≠ 0),a.val,by
    simpa using (mem_piAntidiag.mp a.property).2⟩
  have hm : m.support ⊆ s := filter_subset _ _
  change Real.sqrt (Nat.multinomial s a.val) * ∏ i ∈ s, u i^(a.val i)*normalizedHermite (a.val i) (x i) =
    hermiteLinearCoeff u m * hermiteProduct m x
  unfold hermiteLinearCoeff
  rw [m.multinomial_eq_of_support_subset hm, hermiteProduct_eq_prod_of_support_subset m hm]
  simp only [prod_mul_distrib, mul_assoc]
  have hp : (∏ i ∈ m.support, u i^(m i)) = ∏ i ∈ s, u i^(m i) :=
    prod_subset hm fun i _ hi ↦ by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [hp]
  rfl

end LovaszTheta.Circulant
