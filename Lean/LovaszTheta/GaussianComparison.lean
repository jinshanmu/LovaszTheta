module

public import LovaszTheta.ComparisonInterpolation
public import LovaszTheta.ComparisonRemainder
public import LovaszTheta.ComparisonWalshMoments

/-!
# Quantitative Gaussian comparison for tree coordinates

On the interpolation interval the covariance error contributes a
second moment and the flip error contributes the sum of cubed
derivative weights. The Gaussian law is the centered law with the
variance of the corresponding linear combination of independent normals.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Set
open scoped NNReal Classical

namespace LovaszTheta.Circulant

private lemma comparison_integrand_eq {I B : Type*} [Fintype I] [Fintype B] [DecidableEq B] [Nonempty B]
    (a : I → ℝ) (d : I → ℕ) (c : I → Finset B → ℝ)
    (hd : ∀ i, 0 < d i) (hDegree : ∀ i s, s.card ≠ d i → c i s = 0)
    (f f' : ℝ → ℝ) (v t g : ℝ) (ht : 0 < t) :
    let V := linearWalsh a c
    let W := linearWalsh (fun i ↦ a i/d i) c
    let Γ := comparisonGamma a d c
    ((1/(2*Real.sqrt t)) * average (fun x ↦ V x * f (gaussianBlend t (V x) g)) -
      (v/2) * average (fun x ↦ f' (gaussianBlend t (V x) g))) =
      (1/2) * average (fun x ↦ (Γ x-v)*f' (gaussianBlend t (V x) g)) +
        (1/(8*Real.sqrt t)) * ∑ b : B, average (comparisonRemainder (flip b) V W f f' t g) := by
  let V := linearWalsh a c
  let W := linearWalsh (fun i ↦ a i/d i) c
  let Γ := comparisonGamma a d c
  let F (x : B → Bool) := f (gaussianBlend t (V x) g)
  let G (x : B → Bool) := f' (gaussianBlend t (V x) g)
  let R := ∑ b : B, average (comparisonRemainder (flip b) V W f f' t g)
  have h := average_linear_mul_test_sub_gamma a d c hd hDegree F (fun x ↦ Real.sqrt t * G x)
  change average (fun x ↦ V x*F x) - average (fun x ↦ Γ x*(Real.sqrt t*G x)) = (1/4)*R at h
  have hFactor (x : B → Bool) : Γ x*(Real.sqrt t*G x) = Real.sqrt t*(Γ x*G x) := by ring
  simp_rw [hFactor, average_mul_left] at h
  change (1/(2*Real.sqrt t))*average (fun x ↦ V x*F x) - (v/2)*average G =
    (1/2)*average (fun x ↦ (Γ x-v)*G x) + (1/(8*Real.sqrt t))*R
  simp_rw [sub_mul, average_sub, average_mul_left]
  rw [sub_eq_iff_eq_add.mp h]
  field_simp [(Real.sqrt_pos.mpr ht).ne']
  ring

/-- The sign part of the growth factor, bounded by the even moment
of the linear combination of tree fields. -/
noncomputable def comparisonSignGrowth (D r : ℕ) (A : ℝ) : ℝ :=
  let L := (((2*r-1 : ℕ) : ℝ)^D * A^2 * treeMomentEnvelope D)^r
  Real.sqrt ((3 : ℝ)^(2*r) * (1+L+L))

variable {I : Type*} [Fintype I] {n : ℕ} [NeZero n] [Nonempty (InversionClass n)]

/-- Gaussian comparison with the explicit moment factors before
bounding them by the size and degree envelope. -/
theorem abs_average_treeTest_sub_gaussian_le (a : I → ℝ) (T : I → RootedTree) (k : I → ZMod n)
    {D r : ℕ} (hr : 0 < r) (hD : ∀ i, (T i).nodeCount ≤ D) (hk : ∀ i, RegularFrequency (k i))
    (hDistinct : ∀ i j, Nonempty ((T j).Isomorphism (T i)) →
      (k j = k i ∨ k j = -k i) → i = j)
    (v : ℝ≥0) (hv : (v : ℝ) = ∑ i, a i^2) (C : ℝ) (hC : 0 ≤ C)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (hGrow : ∀ j : ℕ, j ≤ 3 → ∀ x, |iteratedDeriv j ψ x| ≤ C*(1+|x|)^r) :
    let A := ∑ i, |a i|
    let B := treeMomentEnvelope D
    |average (fun x ↦ ψ (linearWalsh a (treeCoefficients T k) x)) -
      ∫ g, ψ g ∂gaussianReal 0 v| ≤
      (C/2) * comparisonSignGrowth D r A * comparisonGaussianGrowth v r *
        (A^2 * (Real.sqrt (B/n) + B/Real.sqrt n) +
          (Real.sqrt ((5 : ℝ)^D))^3 * ((A*Real.sqrt (B/n)) * (A^2*((D : ℝ)*B)))) := by
  let A := ∑ i, |a i|
  let B := treeMomentEnvelope D
  let X := comparisonSignGrowth D r A
  let L := (((2*r-1 : ℕ) : ℝ)^D * A^2 * B)^r
  let H := Real.sqrt ((5 : ℝ)^D)
  let V := linearWalsh a (treeCoefficients T k)
  let W := linearWalsh (fun i ↦ a i/(T i).nodeCount) (treeCoefficients T k)
  let Γ := comparisonGamma a (fun i ↦ (T i).nodeCount) (treeCoefficients T k)
  let δ := treeDelta a T k
  let eΓ := A^2 * (Real.sqrt (B/n) + B/Real.sqrt n)
  let eδ := (A*Real.sqrt (B/n)) * (A^2*((D : ℝ)*B))
  let K := (C/2)*X*(eΓ+H^3*eδ)
  have hK : 0 ≤ K := by unfold K X comparisonSignGrowth eΓ eδ A H B treeMomentEnvelope; positivity
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have heΓ : l2Average (fun x ↦ Γ x-(v : ℝ)) ≤ eΓ := by
    rw [hv]
    exact l2Average_comparisonGamma_sub_variance_le a T k hD hk hDistinct
  have heδ : (∑ b, δ b ^ 3) ≤ eδ := sum_treeDelta_cube_le a T k hD
  have hV : average (fun x ↦ V x^(2*r)) ≤ L := average_linearWalsh_tree_even_pow_le hr a T k hD
  have hXflip (b : InversionClass n) : l2Average (fun x ↦ (1+|V x|+|V (flip b x)|)^r) ≤ X := by
    apply l2Average_growth_le V (fun x ↦ V (flip b x)) r hV
    rw [average_equiv (flip b) (fun x ↦ V x^(2*r))]
    exact hV
  have hXzero : l2Average (fun x ↦ (1+|V x|)^r) ≤ X := by
    have hZero : average (fun _ : InversionClass n → Bool ↦ (0 : ℝ)^(2*r)) ≤ L := by
      simp only [zero_pow (by omega : 2*r ≠ 0), average_const]
      unfold L A B treeMomentEnvelope
      positivity
    change _ ≤ Real.sqrt ((3 : ℝ)^(2*r)*(1+L+L))
    simpa only [abs_zero, add_zero] using l2Average_growth_le V (fun _ ↦ 0) r hV hZero
  have hSixV (b : InversionClass n) :
      average (fun x ↦ updateDifference (flip b) V x ^ 6) ≤ (2*H*δ b)^6 :=
    average_flip_linearWalsh_tree_six_le a T k hD b
  have hSixW (b : InversionClass n) :
      average (fun x ↦ updateDifference (flip b) W x ^ 6) ≤ (2*H*δ b)^6 := by
    apply (average_flip_linearWalsh_tree_six_le (fun i ↦ a i/(T i).nodeCount) T k hD b).trans
    exact pow_le_pow_left₀ (mul_nonneg (by positivity)
      (treeDelta_nonneg (fun i ↦ a i/(T i).nodeCount) T k b))
      (mul_le_mul_of_nonneg_left (treeDelta_div_nodeCount_le a T k b) (by positivity)) _
  have hψ' : ContDiff ℝ 2 (deriv ψ) := hψ.deriv'
  have h1 (x : ℝ) : |ψ x| ≤ C*(1+|x|)^r := by
    simpa only [iteratedDeriv_zero] using hGrow 0 (by decide) x
  have h2 (x : ℝ) : |deriv ψ x| ≤ C*(1+|x|)^r := by
    simpa only [iteratedDeriv_one] using hGrow 1 (by decide) x
  have h3 (x : ℝ) : |deriv (deriv ψ) x| ≤ C*(1+|x|)^r := by
    simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one] using hGrow 2 (by decide) x
  have h4 (x : ℝ) : |iteratedDeriv 2 (deriv ψ) x| ≤ C*(1+|x|)^r := by
    rw [← iteratedDeriv_succ']
    exact hGrow 3 (by decide) x
  let F' (t : ℝ) := ∫ g, (1/(2*Real.sqrt t)) *
    average (fun x ↦ V x * deriv ψ (gaussianBlend t (V x) g)) -
    ((v : ℝ)/2) * average (fun x ↦ deriv (deriv ψ) (gaussianBlend t (V x) g)) ∂gaussianReal 0 v
  have hDer (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (comparisonMean v V ψ) (F' t) t := by
    refine hasDerivAt_comparisonMean_integral v V C r hC ht ?_ ?_ ?_ h1 h2 h3
    · exact fun x ↦ ((hψ.differentiable (by norm_num)) x).hasDerivAt
    · exact fun x ↦ ((hψ'.differentiable (by norm_num)) x).hasDerivAt
    · exact (hψ'.deriv' : ContDiff ℝ 1 (deriv (deriv ψ))).continuous
  have hBound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |F' t| ≤ K*comparisonGaussianGrowth v r := by
    have hIcc := Ioo_subset_Icc_self ht
    have hs := Real.sqrt_pos.mpr ht.1
    have hs₁ : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht.2.le
    have hFlip (g : ℝ) (b : InversionClass n) :
        |average (comparisonRemainder (flip b) V W (deriv ψ) (deriv (deriv ψ)) t g)| ≤
          ((C/2)*t*(1+|g|)^r) * ((2*H*δ b)^3*X) := by
      have hPos : 0 ≤ 2*H*δ b := by exact mul_nonneg (by unfold H; positivity) (treeDelta_nonneg a T k b)
      rw [pow_succ' (2*H*δ b) 2]
      exact abs_average_comparisonRemainder_le (flip b) V W hψ' C r hC h4 hIcc g _
          _ X hPos hPos (hSixW b) (hSixV b) (hXflip b)
    have hPoint (g : ℝ) :
        |(1/(2*Real.sqrt t)) * average (fun x ↦ V x * deriv ψ (gaussianBlend t (V x) g)) -
          ((v : ℝ)/2) * average (fun x ↦ deriv (deriv ψ) (gaussianBlend t (V x) g))| ≤ K*(1+|g|)^r := by
      rw [comparison_integrand_eq a (fun i ↦ (T i).nodeCount) (treeCoefficients T k)
        (fun i ↦ (T i).nodeCount_pos) (fun i _ h ↦ (T i).fieldCoefficient_eq_zero_of_card_ne (k i) h)
        (deriv ψ) (deriv (deriv ψ)) v t g ht.1]
      let P := (1+|g|)^r
      let U := average (fun x ↦ (Γ x-(v : ℝ))*deriv (deriv ψ) (gaussianBlend t (V x) g))
      let R := ∑ b : InversionClass n, average (comparisonRemainder (flip b) V W (deriv ψ) (deriv (deriv ψ)) t g)
      have hCov : |U| ≤ (C*P)*(eΓ*X) :=
        (abs_average_comparison_covariance_le (fun x ↦ Γ x-(v : ℝ)) V C r hC h3 hIcc g).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul heΓ hXzero (l2Average_nonneg _)
            ((l2Average_nonneg _).trans heΓ)) (by positivity))
      have hRem : |R| ≤ (t*8) * ((C/2)*P*X*H^3*(∑ b, δ b^3)) := by
        calc
          _ ≤ ∑ b : InversionClass n, |average (comparisonRemainder (flip b) V W (deriv ψ)
            (deriv (deriv ψ)) t g)| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ b, ((C/2)*t*P) * ((2*H*δ b)^3*X) := sum_le_sum fun b _ ↦ hFlip g b
          _ = _ := by
            have hTerm (b : InversionClass n) :
                ((C/2)*t*P) * ((2*H*δ b)^3*X) = ((t*8)*((C/2)*P*X*H^3)) * δ b^3 := by ring
            simp_rw [hTerm, ← mul_sum]
            ring
      have hScale : (1/(8*Real.sqrt t))*(t*8) = Real.sqrt t := by
        field_simp [hs.ne']
        nlinarith only [Real.sq_sqrt ht.1.le]
      have hRpos : 0 ≤ (C/2)*P*X*H^3 := by unfold P H; positivity
      have hδpos : 0 ≤ ∑ b, δ b^3 :=
        sum_nonneg fun b _ ↦ pow_nonneg (treeDelta_nonneg a T k b) _
      have hRem' : (1/(8*Real.sqrt t))*|R| ≤ (C/2)*P*X*H^3*eδ := by
        calc
          _ ≤ (1/(8*Real.sqrt t))*((t*8)*((C/2)*P*X*H^3*(∑ b, δ b^3))) :=
            mul_le_mul_of_nonneg_left hRem (by positivity)
          _ = Real.sqrt t*((C/2)*P*X*H^3*(∑ b, δ b^3)) := by rw [← mul_assoc, hScale]
          _ ≤ (C/2)*P*X*H^3*(∑ b, δ b^3) :=
            mul_le_of_le_one_left (mul_nonneg hRpos hδpos) hs₁
          _ ≤ _ := mul_le_mul_of_nonneg_left heδ hRpos
      change |(1/2)*U + (1/(8*Real.sqrt t))*R| ≤ K*P
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ)),
        abs_of_nonneg (by positivity : 0 ≤ 1/(8*Real.sqrt t))]
      refine (add_le_add (mul_le_mul_of_nonneg_left hCov (by norm_num)) hRem').trans_eq ?_
      unfold K
      ring
    have hi : |F' t| ≤ K*(∫ g, (1+|g|)^r ∂gaussianReal 0 v) := by
      unfold F'
      rw [← Real.norm_eq_abs, ← integral_const_mul]
      exact norm_integral_le_of_norm_le ((integrable_one_add_abs_pow_gaussian v r).const_mul K)
        (ae_of_all _ fun g ↦ by simpa only [Real.norm_eq_abs] using hPoint g)
    exact hi.trans (mul_le_mul_of_nonneg_left (integral_one_add_abs_pow_gaussian_le v r) hK)
  have h := abs_comparisonMean_sub_le_of_bound v V ψ (K*comparisonGaussianGrowth v r) F'
    (continuousOn_comparisonMean v V C r hC hψ.continuous h1) hDer hBound
  refine h.trans_eq ?_
  unfold K eΓ eδ
  ring

end LovaszTheta.Circulant
