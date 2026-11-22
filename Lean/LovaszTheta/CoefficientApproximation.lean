module

public import LovaszTheta.ConstructionSymmetry
public import LovaszTheta.ClosureMatrices

/-!
# The coefficient error through finite depth

At depth (h+1), the new closures have the old coefficients
scaled separately in each arity. The scale tends to one and the
mass newly added at depth (h+1) tends to zero.
-/

@[expose] public section

open Finset Filter
open scoped Classical Topology

namespace LovaszTheta.Independent.Construction

variable {N : ℕ}

/-- The support of the included previous array. -/
noncomputable def previousTrees (N h : ℕ) : Finset (Construction N (h+1)) :=
  univ.image (widen N h)

lemma widen_mem_previousTrees (h : ℕ) (t : Construction N h) : widen N h t ∈ previousTrees N h :=
  mem_image_of_mem _ (mem_univ _)

lemma leaf_mem_previousTrees (h : ℕ) : leaf (N := N) (h+1) ∈ previousTrees N h := by
  simpa only [widen_leaf] using widen_mem_previousTrees h (leaf (N := N) h)

/-- The normalized previous array padded with zeros on the new shapes. -/
noncomputable def paddedCoefficient (N h : ℕ) (t : Construction N (h+1)) : ℝ :=
  if t ∈ previousTrees N h then coefficient N (h+1) t / Real.sqrt (mass N h) else 0

lemma paddedCoefficient_widen (h : ℕ) (t : Construction N h) :
    paddedCoefficient N h (widen N h t) = normalized N h t := by
  rw [paddedCoefficient,ite_eq_left (widen_mem_previousTrees h t),coefficient_widen]
  rfl

/-- The new array obtained by closing tuples of normalized previous coefficients. -/
noncomputable def closedCoefficient (N h : ℕ) : Construction N (h+1) → ℝ
  | .inl _ => 0
  | .inr ⟨j,w⟩ => bernsteinCoefficient N j.val * wordWeight (normalized N h) w

/-- The leaf summand of the previous array, in the larger array. -/
noncomputable def leafCoefficient (N h : ℕ) (t : Construction N (h+1)) : ℝ :=
  if t = leaf (h+1) then normalized N h (leaf h) else 0

/-- The coefficient difference after joining the leaf and closing the nonlinear terms. -/
noncomputable def difference (N h : ℕ) (t : Construction N (h+1)) : ℝ :=
  closedCoefficient N h t + leafCoefficient N h t - paddedCoefficient N h t

private lemma previousTrees_reverse_iff (h : ℕ) (t : Construction N (h+1)) :
    reverse N (h+1) t ∈ previousTrees N h ↔ t ∈ previousTrees N h := by
  have hStep (s : Construction N (h+1)) (hs : s ∈ previousTrees N h) :
      reverse N (h+1) s ∈ previousTrees N h := by
    obtain ⟨u,_,rfl⟩ := mem_image.mp hs
    rw [← widen_reverse]
    exact widen_mem_previousTrees h _
  exact ⟨fun ht ↦ (reverse_involutive N (h+1) t) ▸ hStep _ ht,hStep t⟩

lemma difference_reverse (N h : ℕ) (t : Construction N (h+1)) :
    difference N h (reverse N (h+1) t) = difference N h t := by
  have hP : paddedCoefficient N h (reverse N (h+1) t) = paddedCoefficient N h t := by
    by_cases ht : t ∈ previousTrees N h
    · rw [paddedCoefficient,paddedCoefficient,ite_eq_left ((previousTrees_reverse_iff h t).mpr ht),
        ite_eq_left ht,coefficient_reverse]
    · have hn : reverse N (h+1) t ∉ previousTrees N h := ht ∘ (previousTrees_reverse_iff h t).mp
      rw [paddedCoefficient,paddedCoefficient,ite_eq_right hn,ite_eq_right ht]
  have hL : leafCoefficient N h (reverse N (h+1) t) = leafCoefficient N h t := by
    unfold leafCoefficient
    have he : reverse N (h+1) t = leaf (h+1) ↔ t = leaf (h+1) := by
      rw [← reverse_leaf (N := N) (h+1)]
      exact (reverse_involutive N (h+1)).injective.eq_iff
    simp only [he]
  have hC : closedCoefficient N h (reverse N (h+1) t) = closedCoefficient N h t := by
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
    rcases t with (t | ⟨j,w⟩)
    · rfl
    · change bernsteinCoefficient N j.val * (∏ i : Fin j.val, normalized N h (reverse N h (w i.rev))) =
        bernsteinCoefficient N j.val * (∏ i, normalized N h (w i))
      simp only [normalized_reverse]
      congr 1
      exact Fintype.prod_equiv Fin.revPerm _ _ fun _ ↦ rfl
  rw [difference,difference,hC,hL,hP]

private lemma closedCoefficient_node_scale (N h : ℕ) (j : nonlinearDegrees N)
    (w : Fin j.val → Construction N h) :
    closedCoefficient N h (node h j w) =
      coefficient N (h+1) (node h j w) * ((Real.sqrt (mass N h))⁻¹)^j.val := by
  change bernsteinCoefficient N j.val*(∏ i, coefficient N h (w i)/Real.sqrt (mass N h)) = _
  simp_rw [div_eq_mul_inv]
  rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,coefficient_node,mul_assoc]

private lemma difference_leaf (N h : ℕ) : difference N h (leaf (h+1)) = 0 := by
  rw [← widen_leaf]
  have hpad := paddedCoefficient_widen h (leaf (N := N) h)
  rw [difference,hpad,widen_leaf]
  simp [leafCoefficient,closedCoefficient,leaf]

/-- The total discrepancy in the arity-dependent normalization multipliers. -/
noncomputable def multiplierError (N h : ℕ) : ℝ :=
  ∑ j ∈ nonlinearDegrees N, |((Real.sqrt (mass N h))⁻¹)^j-(Real.sqrt (mass N h))⁻¹|

private lemma abs_difference_le (N h : ℕ) (t : Construction N (h+1)) :
    |difference N h t| ≤ |coefficient N (h+1) t| *multiplierError N h +
      if t ∈ previousTrees N h then 0 else |coefficient N (h+1) t| * |(Real.sqrt (mass N h))⁻¹| := by
  let r := (Real.sqrt (mass N h))⁻¹
  change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at t
  rcases t with (t | ⟨j,w⟩)
  · cases t
    change |difference N h (leaf (h+1))| ≤ _
    rw [difference_leaf,abs_zero]
    have h : 0 ≤ multiplierError N h := sum_nonneg fun _ _ ↦ abs_nonneg _
    split_ifs <;> positivity
  · let t := node h j w
    let a := coefficient N (h+1) t
    have hArity : |r^j.val-r| ≤ multiplierError N h :=
      single_le_sum (f := fun k : ℕ ↦ |r^k-r|) (fun _ _ ↦ abs_nonneg _) j.property
    have hLeaf : t ≠ leaf (h+1) := by
      change (Sum.inr ⟨j,w⟩ : Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h)) ≠ Sum.inl ()
      intro he
      cases he
    change |difference N h t| ≤ _
    rw [difference,leafCoefficient,ite_eq_right hLeaf,add_zero,closedCoefficient_node_scale,paddedCoefficient]
    change |a*r^j.val-(if t ∈ previousTrees N h then a/Real.sqrt (mass N h) else 0)| ≤
      |a| * multiplierError N h+(if t ∈ previousTrees N h then 0 else |a| * |r|)
    split_ifs with ht
    · rw [div_eq_mul_inv,← mul_sub,abs_mul,add_zero]
      exact mul_le_mul_of_nonneg_left hArity (abs_nonneg _)
    · rw [sub_zero]
      have he : a*r^j.val = a*(r^j.val-r)+a*r := by ring
      rw [he]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hArity (abs_nonneg _)) le_rfl

/-- Squared coefficient error, controlled by the changes in scale and in depth mass. -/
theorem sum_sq_difference_le (N h : ℕ) :
    (∑ t, (difference N h t)^2) ≤ 2*((multiplierError N h)^2*mass N (h+1) +
      ((Real.sqrt (mass N h))⁻¹)^2*(mass N (h+1)-mass N h)) := by
  let K := multiplierError N h
  let r := (Real.sqrt (mass N h))⁻¹
  let a (t : Construction N (h+1)) := coefficient N (h+1) t
  let f (t : Construction N (h+1)) := |a t| *K
  let g (t : Construction N (h+1)) := if t ∈ previousTrees N h then 0 else |a t| * |r|
  have h₁ (t : Construction N (h+1)) : (difference N h t)^2 ≤ 2*((f t)^2+(g t)^2) := by
    have he := abs_difference_le N h t
    have he' : |difference N h t|^2 ≤ (f t+g t)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) he _
    rw [sq_abs] at he'
    nlinarith only [he',sq_nonneg (f t-g t)]
  have hF : (∑ t, (f t)^2) = K^2*mass N (h+1) := by
    simp only [f,mul_pow,sq_abs,mass,a,← sum_mul]
    ring
  have hG : (∑ t, (g t)^2) = r^2*(mass N (h+1)-mass N h) := by
    have he (t : Construction N (h+1)) :
        (g t)^2 = if t ∉ previousTrees N h then (a t)^2*r^2 else 0 := by
      unfold g
      by_cases ht : t ∈ previousTrees N h <;> simp [ht,mul_pow,sq_abs]
    simp_rw [he,← sum_filter,← sum_mul]
    have hs : (∑ t ∈ univ.filter (fun t ↦ t ∉ previousTrees N h), (a t)^2) =
        mass N (h+1)-mass N h := by
      have hsum := sum_filter_add_sum_filter_not (s := (univ : Finset (Construction N (h+1))))
        (p := (· ∈ previousTrees N h)) (fun t ↦ (a t)^2)
      have hi : (univ.filter (· ∈ previousTrees N h)) = previousTrees N h := by
        rw [filter_mem_eq_inter,univ_inter]
      rw [hi] at hsum
      change (∑ t ∈ univ.image (widen N h), (a t)^2) + _ = _ at hsum
      rw [sum_sq_widen_image] at hsum
      change mass N h + _ = mass N (h+1) at hsum
      linarith
    rw [hs,mul_comm]
  exact (sum_le_sum (fun t _ ↦ h₁ t)).trans_eq (by rw [← mul_sum,sum_add_distrib,hF,hG])

/-- The norm of the difference tends to zero as the depth cutoff is increased. -/
theorem tendsto_differenceNorm {N : ℕ} (hN : 0 < N) :
    Tendsto (fun h : ℕ ↦ Real.sqrt (∑ t, (difference N h t)^2)) atTop (𝓝 0) := by
  have hm := tendsto_mass hN
  have hr : Tendsto (fun h : ℕ ↦ (Real.sqrt (mass N h))⁻¹) atTop (𝓝 1) := by
    have hs := hm.sqrt
    rw [Real.sqrt_one] at hs
    simpa only [inv_one] using hs.inv₀ one_ne_zero
  have hK : Tendsto (multiplierError N) atTop (𝓝 0) := by
    unfold multiplierError
    have h (j : ℕ) : Tendsto (fun h : ℕ ↦ |((Real.sqrt (mass N h))⁻¹)^j-(Real.sqrt (mass N h))⁻¹|)
        atTop (𝓝 0) := by
      simpa only [one_pow,sub_self,abs_zero] using ((hr.pow j).sub hr).abs
    simpa only [sum_const_zero] using tendsto_finsetSum (nonlinearDegrees N) (fun j _ ↦ h j)
  have hNext := hm.comp (tendsto_add_atTop_nat 1)
  have hUpper : Tendsto (fun h : ℕ ↦ 2*((multiplierError N h)^2*mass N (h+1) +
      ((Real.sqrt (mass N h))⁻¹)^2*(mass N (h+1)-mass N h))) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul,one_pow,sub_self,mul_zero,add_zero,Function.comp_apply] using
      (((hK.pow 2).mul hNext).add ((hr.pow 2).mul (hNext.sub hm))).const_mul (2 : ℝ)
  have hSum : Tendsto (fun h : ℕ ↦ ∑ t, (difference N h t)^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
      (Eventually.of_forall fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)
      (Eventually.of_forall (sum_sq_difference_le N))
  simpa only [Real.sqrt_zero] using hSum.sqrt

end LovaszTheta.Independent.Construction
