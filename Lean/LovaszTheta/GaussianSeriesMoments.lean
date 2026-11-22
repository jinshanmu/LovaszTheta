module

public import LovaszTheta.GaussianSeriesLaw
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Higher moments of Gaussian series

The difference between two sums is itself a centered Gaussian,
so convergence of the coefficients in ℓ² gives convergence in
every finite Lp space. Hölder's inequality then gives continuity
of polynomial evaluation in L².
-/

@[expose] public section

open Finset Filter MeasureTheory ProbabilityTheory Polynomial
open scoped Classical ENNReal NNReal Polynomial

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- Scaling the standard normal by the coefficient norm gives the law of the series. -/
lemma map_gaussianSeries_eq_scaled (a : lp (fun _ : I ↦ ℝ) 2) :
    (gaussianProduct I).map (gaussianSeries I a) =
      (gaussianReal 0 1).map (fun z ↦ ‖a‖*z) := by
  rw [map_gaussianSeries,gaussianReal_map_const_mul,mul_zero,mul_one]
  congr 1
  apply NNReal.eq
  exact Real.coe_toNNReal _ (sq_nonneg _)

lemma memLp_gaussianSeries (a : lp (fun _ : I ↦ ℝ) 2) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (gaussianSeries I a) p (gaussianProduct I) := by
  have h := memLp_id_gaussianReal' (μ := 0) (v := (‖a‖^2).toNNReal) p hp
  rw [← map_gaussianSeries a] at h
  exact h.comp_of_map ((Lp.memLp _).aestronglyMeasurable.aemeasurable)

lemma eLpNorm_gaussianSeries (a : lp (fun _ : I ↦ ℝ) 2) (p : ℝ≥0∞) :
    eLpNorm (gaussianSeries I a) p (gaussianProduct I) =
      ENNReal.ofReal ‖a‖ * eLpNorm id p (gaussianReal 0 1) := by
  change eLpNorm (id ∘ (gaussianSeries I a : (I → ℝ) → ℝ)) p (gaussianProduct I) = _
  rw [← eLpNorm_map_measure (by fun_prop) ((Lp.memLp (gaussianSeries I a)).aestronglyMeasurable.aemeasurable),
    map_gaussianSeries_eq_scaled, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  change eLpNorm (‖a‖ • (id : ℝ → ℝ)) p (gaussianReal 0 1) = _
  rw [eLpNorm_const_smul, ← ofReal_norm,Real.norm_of_nonneg (norm_nonneg _)]

/-- The same Gaussian series, regarded in any finite Lp. -/
noncomputable def gaussianSeriesInLp (p : ℝ≥0∞) (hp : p ≠ ∞) (a : lp (fun _ : I ↦ ℝ) 2) :
    Lp ℝ p (gaussianProduct I) :=
  (memLp_gaussianSeries a p hp).toLp (gaussianSeries I a)

lemma gaussianSeriesInLp_ae_eq (p : ℝ≥0∞) (hp : p ≠ ∞) (a : lp (fun _ : I ↦ ℝ) 2) :
    gaussianSeriesInLp p hp a =ᵐ[gaussianProduct I] gaussianSeries I a :=
  MemLp.coeFn_toLp _

theorem continuous_gaussianSeriesInLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Continuous (gaussianSeriesInLp (I := I) p hp) := by
  let c := (eLpNorm id p (gaussianReal 0 1)).toReal
  let L : lp (fun _ : I ↦ ℝ) 2 →ₗ[ℝ] Lp ℝ p (gaussianProduct I) :=
    { toFun := gaussianSeriesInLp p hp
      map_add' := fun a b ↦ by
        apply Lp.ext
        filter_upwards [gaussianSeriesInLp_ae_eq p hp (a+b),gaussianSeriesInLp_ae_eq p hp a,
          gaussianSeriesInLp_ae_eq p hp b,Lp.coeFn_add (gaussianSeriesInLp p hp a) (gaussianSeriesInLp p hp b),
          Lp.coeFn_add (gaussianSeries I a) (gaussianSeries I b)] with x h h₁ h₂ h₃ h₄
        rw [h,map_add,h₄,h₃,Pi.add_apply,Pi.add_apply,h₁,h₂]
      map_smul' := fun r a ↦ by
        apply Lp.ext
        filter_upwards [gaussianSeriesInLp_ae_eq p hp (r • a),gaussianSeriesInLp_ae_eq p hp a,
          Lp.coeFn_smul r (gaussianSeriesInLp p hp a),Lp.coeFn_smul r (gaussianSeries I a)] with x h h₁ h₂ h₃
        rw [h,map_smul,h₃,RingHom.id_apply,h₂,Pi.smul_apply,Pi.smul_apply,h₁] }
  have hL (a : lp (fun _ : I ↦ ℝ) 2) : ‖L a‖ ≤ c*‖a‖ := by
    change ‖gaussianSeriesInLp p hp a‖ ≤ _
    rw [gaussianSeriesInLp,Lp.norm_toLp,eLpNorm_gaussianSeries,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg _),mul_comm]
  exact (L.mkContinuous c hL).continuous

private theorem exists_continuous_gaussianPower (j : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ F : lp (fun _ : I ↦ ℝ) 2 → Lp ℝ p (gaussianProduct I),
      Continuous F ∧ ∀ a, F a =ᵐ[gaussianProduct I] fun x ↦ (gaussianSeries I a x)^j := by
  induction j generalizing p with
  | zero =>
    let f : (I → ℝ) → ℝ := fun _ ↦ 1
    exact ⟨fun _ ↦ (memLp_const 1).toLp f,continuous_const,fun _ ↦ by
      simpa only [pow_zero] using MemLp.coeFn_toLp (memLp_const (μ := gaussianProduct I) (p := p) (1 : ℝ))⟩
  | succ j ih =>
    let μ := gaussianProduct I
    let q := ENNReal.ofReal (2*p.toReal)
    have hP : 1 ≤ p.toReal := by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
    have hp' : 1 ≤ 2*p.toReal := by linarith
    let _ : Fact (1 ≤ q) := ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp'⟩
    have hReal : Real.HolderTriple (2*p.toReal) (2*p.toReal) p.toReal :=
      ⟨by field_simp; ring, by linarith, by linarith⟩
    let _ : ENNReal.HolderTriple q q p := by
      simpa only [ENNReal.ofReal_toReal hp] using hReal.ennrealOfReal
    obtain ⟨F,hF,hEq⟩ := ih q ENNReal.ofReal_ne_top
    let A := gaussianSeriesInLp (I := I) q ENNReal.ofReal_ne_top
    let M := (ContinuousLinearMap.mul ℝ ℝ).holderL μ q q p
    refine ⟨fun a ↦ M (F a) (A a), M.continuous₂.comp (hF.prodMk
      (continuous_gaussianSeriesInLp _ ENNReal.ofReal_ne_top)),?_⟩
    intro a
    filter_upwards [((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (F a) (A a)),
      hEq a,gaussianSeriesInLp_ae_eq q ENNReal.ofReal_ne_top a] with x hM h₁ h₂
    change (M (F a) (A a)) x = _
    exact hM.trans (by change (F a) x * gaussianSeriesInLp q ENNReal.ofReal_ne_top a x = _; rw [h₁,h₂,pow_succ])

/-- Each polynomial can be evaluated continuously in L² on the Gaussian series. -/
theorem exists_continuous_gaussianPolynomial (P : ℝ[X]) :
    ∃ F : lp (fun _ : I ↦ ℝ) 2 → Lp ℝ 2 (gaussianProduct I),
      Continuous F ∧ ∀ a, F a =ᵐ[gaussianProduct I] fun x ↦ P.eval (gaussianSeries I a x) := by
  have h (j : ℕ) :
      ∃ f : lp (fun _ : I ↦ ℝ) 2 → Lp ℝ 2 (gaussianProduct I), Continuous f ∧
        ∀ a, f a =ᵐ[gaussianProduct I] fun x ↦ (gaussianSeries I a x)^j :=
    exists_continuous_gaussianPower j 2 (by norm_num)
  choose f hf he using h
  refine ⟨fun a ↦ ∑ j ∈ P.support, P.coeff j • f j a, ?_, ?_⟩
  · exact continuous_finsetSum _ (fun j _ ↦ (continuous_const_smul (P.coeff j)).comp (hf j))
  · intro a
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    have hTerms (j : ℕ) : (P.coeff j • f j a : Lp ℝ 2 (gaussianProduct I)) =ᵐ[gaussianProduct I]
      fun x ↦ P.coeff j * (gaussianSeries I a x)^j :=
      (Lp.coeFn_smul _ _).trans ((he j a).mono fun x hx ↦ by simp only [Pi.smul_apply,smul_eq_mul,hx])
    refine (eventuallyEq_sum fun j _ ↦ hTerms j).trans (Eventually.of_forall fun x ↦ ?_)
    simp only [Finset.sum_apply,eval_eq_sum,Polynomial.sum]

end LovaszTheta.Circulant
