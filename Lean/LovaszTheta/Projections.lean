module

public import LovaszTheta.Program
public import LovaszTheta.Residual

/-!
# The real Fourier projections

The two connection constraints and the constant mode describe three
orthogonal summands. The difference of the first two projections is
the operator in the smoothed equation.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The nonzero residues outside the connection set. -/
def nonconnectionSet (x : InversionClass n → Bool) : Set (ZMod n) :=
  {s | epsilon x s = 1}

/-- The projection matrix on real spatial coordinates. -/
noncomputable def realProjection (S : Set (ZMod n)) : Matrix (ZMod n) (ZMod n) ℝ :=
  (fourierProjection S).map Complex.re

private lemma fourierProjection_apply (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (i j : ZMod n) :
    fourierProjection S i j =
      (n : ℂ)⁻¹ * ∑ s, if s ∈ S then ZMod.stdAddChar (-((i - j) * s)) else 0 := by
  dsimp [fourierProjection, multiplier]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, fourierMatrix_conjTranspose_apply]
  congr 1
  apply sum_congr rfl
  intro s _
  by_cases h : s ∈ S
  · simp only [ite_eq_left h, mul_one, fourierMatrix, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  · simp [h]

private lemma star_fourierProjection_apply (S : Set (ZMod n)) (i j : ZMod n) :
    star (fourierProjection S i j) = fourierProjection S j i := by
  classical
  rw [fourierProjection_apply, fourierProjection_apply, star_mul, star_inv₀]
  have hn : star (n : ℂ) = n := by simp
  rw [hn, star_sum]
  rw [mul_comm (∑ s, star (if s ∈ S then ZMod.stdAddChar (-((i - j) * s)) else 0))
    ((n : ℂ)⁻¹)]
  congr 1
  apply sum_congr rfl
  intro s _
  by_cases h : s ∈ S
  · simp only [ite_eq_left h, star_stdAddChar, ← neg_mul, neg_sub]
  · simp [h]

private lemma fourierProjection_neg_neg (S : Set (ZMod n)) (i j : ZMod n) :
    fourierProjection S (-i) (-j) = fourierProjection S j i := by
  classical
  simp only [fourierProjection_apply, neg_sub_neg]

private lemma fourierProjection_apply_swap (S : Set (ZMod n))
    (hS : ∀ s, -s ∈ S ↔ s ∈ S) (i j : ZMod n) :
    fourierProjection S j i = fourierProjection S i j := by
  classical
  rw [fourierProjection_apply, fourierProjection_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun s ↦ ?_
  simp only [Equiv.neg_apply, hS, mul_neg, ← neg_mul, neg_sub]

lemma complexify_realProjection (S : Set (ZMod n)) (hS : ∀ s, -s ∈ S ↔ s ∈ S) :
    (realProjection S).map Complex.ofReal = fourierProjection S := by
  ext i j
  have h := (star_fourierProjection_apply S i j).trans (fourierProjection_apply_swap S hS i j)
  change ((fourierProjection S i j).re : ℂ) = fourierProjection S i j
  apply Complex.ext
  · simp
  · have hIm := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hIm
    simp only [Complex.ofReal_im]
    linarith

lemma realProjection_isSymm (S : Set (ZMod n)) : (realProjection S).IsSymm := by
  ext i j
  change (fourierProjection S j i).re = (fourierProjection S i j).re
  rw [← star_fourierProjection_apply S i j]
  simp

lemma realProjection_even (S : Set (ZMod n)) {v : ZMod n → ℝ} (hv : v.Even) :
    (realProjection S *ᵥ v).Even := by
  intro i
  unfold Matrix.mulVec dotProduct
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun j ↦ ?_
  change (fourierProjection S (-i) j).re * v j = (fourierProjection S i (-j)).re * v (-j)
  rw [hv j, show fourierProjection S (-i) j = fourierProjection S (-j) i by
    rw [← fourierProjection_neg_neg S i (-j), neg_neg]]
  congr 1
  exact (realProjection_isSymm S).apply i (-j)

lemma realProjection_mulVec_eq_zero_iff (S : Set (ZMod n))
    (hS : ∀ s, -s ∈ S ↔ s ∈ S) (v : ZMod n → ℝ) :
    realProjection S *ᵥ v = 0 ↔
      fourierProjection S *ᵥ (fun i ↦ (v i : ℂ)) = 0 := by
  have hV := funext (RingHom.map_mulVec Complex.ofRealHom (realProjection S) v)
  change (fun i ↦ ((realProjection S *ᵥ v) i : ℂ)) =
    (realProjection S).map Complex.ofReal *ᵥ (fun i ↦ (v i : ℂ)) at hV
  rw [complexify_realProjection S hS] at hV
  rw [← hV]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    funext i
    exact Complex.ofReal_eq_zero.mp (congrFun h i)

private lemma fourierProjection_idempotent (S : Set (ZMod n)) :
    fourierProjection S * fourierProjection S = fourierProjection S := by
  classical
  unfold fourierProjection
  rw [multiplier_mul]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

private lemma fourierProjection_mul_of_disjoint {S T : Set (ZMod n)} (h : Disjoint S T) :
    fourierProjection S * fourierProjection T = 0 := by
  classical
  unfold fourierProjection
  rw [multiplier_mul, show (fun i ↦
      (if i ∈ S then (1 : ℂ) else 0) * (if i ∈ T then 1 else 0)) = 0 by
    funext i
    by_cases hi : i ∈ S
    · simp [hi, Set.disjoint_left.mp h hi]
    · simp [hi]]
  simp [multiplier]

lemma realProjection_idempotent (S : Set (ZMod n)) (hS : ∀ s, -s ∈ S ↔ s ∈ S) :
    realProjection S * realProjection S = realProjection S := by
  apply Matrix.map_injective Complex.ofReal_injective
  have hMap := Matrix.map_mul (f := Complex.ofRealHom) (L := realProjection S)
    (M := realProjection S)
  change (realProjection S * realProjection S).map Complex.ofReal =
      (realProjection S).map Complex.ofReal * (realProjection S).map Complex.ofReal at hMap
  change (realProjection S * realProjection S).map Complex.ofReal =
    (realProjection S).map Complex.ofReal
  rw [hMap, complexify_realProjection S hS, fourierProjection_idempotent]

lemma realProjection_mul_of_disjoint {S T : Set (ZMod n)} (hS : ∀ s, -s ∈ S ↔ s ∈ S)
    (hT : ∀ s, -s ∈ T ↔ s ∈ T) (h : Disjoint S T) :
    realProjection S * realProjection T = 0 := by
  apply Matrix.map_injective Complex.ofReal_injective
  have hMap := Matrix.map_mul (f := Complex.ofRealHom) (L := realProjection S)
    (M := realProjection T)
  change (realProjection S * realProjection T).map Complex.ofReal =
      (realProjection S).map Complex.ofReal * (realProjection T).map Complex.ofReal at hMap
  change (realProjection S * realProjection T).map Complex.ofReal =
    (0 : Matrix (ZMod n) (ZMod n) ℝ).map Complex.ofReal
  rw [hMap, complexify_realProjection S hS, complexify_realProjection T hT,
    fourierProjection_mul_of_disjoint h]
  simp

lemma realProjection_zero_apply (i j : ZMod n) :
    realProjection ({0} : Set (ZMod n)) i j = (n : ℝ)⁻¹ := by
  classical
  change (fourierProjection ({0} : Set (ZMod n)) i j).re = _
  rw [fourierProjection_apply]
  simp only [Set.mem_singleton_iff, Finset.sum_ite_eq', mem_univ, ite_true, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, mul_one, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.ofReal_re]

lemma realProjection_zero_mulVec (v : ZMod n → ℝ) :
    realProjection ({0} : Set (ZMod n)) *ᵥ v = meanVector v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, realProjection_zero_apply, ← mul_sum, meanVector, mass,
    ZMod.card]
  ring

omit [NeZero n] in
lemma connectionSet_even (x : InversionClass n → Bool) (s : ZMod n) :
    -s ∈ connectionSet x ↔ s ∈ connectionSet x := by
  change epsilon x (-s) = -1 ↔ epsilon x s = -1
  rw [epsilon_even]

omit [NeZero n] in
lemma nonconnectionSet_even (x : InversionClass n → Bool) (s : ZMod n) :
    -s ∈ nonconnectionSet x ↔ s ∈ nonconnectionSet x := by
  change epsilon x (-s) = 1 ↔ epsilon x s = 1
  rw [epsilon_even]

omit [NeZero n] in
lemma zeroSet_even (s : ZMod n) : -s ∈ ({0} : Set (ZMod n)) ↔ s ∈ ({0} : Set (ZMod n)) := by
  simp

omit [NeZero n] in
lemma connection_nonconnection_disjoint (x : InversionClass n → Bool) :
    Disjoint (connectionSet x) (nonconnectionSet x) := by
  refine Set.disjoint_left.mpr fun s hs ht ↦ ?_
  change epsilon x s = -1 at hs
  change epsilon x s = 1 at ht
  linarith

omit [NeZero n] in
lemma connection_zero_disjoint (x : InversionClass n → Bool) :
    Disjoint (connectionSet x) ({0} : Set (ZMod n)) := by
  refine Set.disjoint_left.mpr fun s hs ht ↦ ?_
  rw [Set.mem_singleton_iff.mp ht] at hs
  change epsilon x 0 = -1 at hs
  norm_num at hs

omit [NeZero n] in
lemma nonconnection_zero_disjoint (x : InversionClass n → Bool) :
    Disjoint (nonconnectionSet x) ({0} : Set (ZMod n)) := by
  refine Set.disjoint_left.mpr fun s hs ht ↦ ?_
  rw [Set.mem_singleton_iff.mp ht] at hs
  change epsilon x 0 = 1 at hs
  norm_num at hs

private lemma complex_projection_sum (x : InversionClass n → Bool) :
    fourierProjection (connectionSet x) + fourierProjection (nonconnectionSet x) +
      fourierProjection ({0} : Set (ZMod n)) = 1 := by
  classical
  unfold fourierProjection multiplier
  rw [← smul_add, ← smul_add, ← Matrix.add_mul, ← Matrix.add_mul,
    ← Matrix.mul_add, ← Matrix.mul_add, Matrix.diagonal_add, Matrix.diagonal_add]
  have hOne : (fun i : ZMod n ↦
      (if i ∈ connectionSet x then (1 : ℂ) else 0) +
      (if i ∈ nonconnectionSet x then 1 else 0) + (if i = 0 then 1 else 0)) = 1 := by
    funext i
    change (if epsilon x i = -1 then (1 : ℂ) else 0) +
      (if epsilon x i = 1 then 1 else 0) + (if i = 0 then 1 else 0) = 1
    by_cases hi : i = 0
    · subst i
      norm_num
    · cases hx : x (inversionClass i hi) <;> norm_num [epsilon, hi, hx]
  simp only [Set.mem_singleton_iff]
  rw [hOne, Matrix.diagonal_one', mul_one, fourierMatrix_mul_conjTranspose, smul_smul]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp [hn]

lemma real_projection_sum (x : InversionClass n → Bool) :
    realProjection (connectionSet x) + realProjection (nonconnectionSet x) +
      realProjection ({0} : Set (ZMod n)) = 1 := by
  ext i j
  have h := congrArg (fun A : Matrix (ZMod n) (ZMod n) ℂ ↦ (A i j).re)
    (complex_projection_sum x)
  by_cases hEq : i = j
  · subst j
    simpa [realProjection, Complex.add_re] using h
  · simpa [realProjection, Matrix.one_apply_ne hEq, Complex.add_re] using h

/-- The difference between the nonconnection and connection projections. -/
noncomputable def signOperator (x : InversionClass n → Bool) :
    (ZMod n → ℝ) →ₗ[ℝ] ZMod n → ℝ :=
  (realProjection (nonconnectionSet x) - realProjection (connectionSet x)).mulVecLin

lemma signOperator_apply (x : InversionClass n → Bool) (v : ZMod n → ℝ) :
    signOperator x v =
      realProjection (nonconnectionSet x) *ᵥ v - realProjection (connectionSet x) *ᵥ v := by
  exact Matrix.sub_mulVec _ _ _

lemma realProjection_selfAdjoint (S : Set (ZMod n)) (v w : ZMod n → ℝ) :
    (realProjection S *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (realProjection S *ᵥ w) := by
  calc
    _ = w ⬝ᵥ (realProjection S *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (realProjection S)ᵀ *ᵥ w := (Matrix.dotProduct_transpose_mulVec _ _ _).symm
    _ = _ := by rw [(realProjection_isSymm S).eq]

lemma signOperator_selfAdjoint (x : InversionClass n → Bool) (v w : ZMod n → ℝ) :
    signOperator x v ⬝ᵥ w = v ⬝ᵥ signOperator x w := by
  simp only [signOperator_apply, sub_dotProduct, dotProduct_sub, realProjection_selfAdjoint]

lemma signOperator_square (x : InversionClass n → Bool) (v : ZMod n → ℝ) :
    signOperator x (signOperator x v) = v - meanVector v := by
  have hSquare :
      (realProjection (nonconnectionSet x) - realProjection (connectionSet x)) *
        (realProjection (nonconnectionSet x) - realProjection (connectionSet x)) =
      1 - realProjection ({0} : Set (ZMod n)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, realProjection_idempotent _ (nonconnectionSet_even x),
      realProjection_idempotent _ (connectionSet_even x),
      realProjection_mul_of_disjoint (connectionSet_even x) (nonconnectionSet_even x)
        (connection_nonconnection_disjoint x),
      realProjection_mul_of_disjoint (nonconnectionSet_even x) (connectionSet_even x)
        (connection_nonconnection_disjoint x).symm, sub_zero, zero_sub, sub_neg_eq_add,
      add_comm, eq_sub_iff_add_eq]
    exact real_projection_sum x
  change (realProjection (nonconnectionSet x) - realProjection (connectionSet x)) *ᵥ
    ((realProjection (nonconnectionSet x) - realProjection (connectionSet x)) *ᵥ v) = _
  rw [Matrix.mulVec_mulVec, hSquare, Matrix.sub_mulVec, Matrix.one_mulVec, realProjection_zero_mulVec]

end LovaszTheta.Circulant
