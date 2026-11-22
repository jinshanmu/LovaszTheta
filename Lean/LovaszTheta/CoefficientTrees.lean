module

public import LovaszTheta.ChainBasics
public import LovaszTheta.ChainReversal
public import LovaszTheta.CertificatePolynomial
public import Mathlib.Data.List.OfFn

/-!
# The coefficient arrays at finite depth

The single edge is the leaf. A node specifies an ordered tuple of
smaller shapes and closes their chain. Injectivity of closure makes
the coefficients unique, and the squared norm has the manuscript's
depth recurrence.
-/

@[expose] public section

open Finset Filter
open scoped Classical Topology

namespace LovaszTheta.Independent

/-- Trees of height at most the given depth, with allowed arities (2,ldots,N). -/
abbrev Construction (N : ℕ) : ℕ → Type
  | 0 => Unit
  | h+1 => Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h)

namespace Construction

variable {N : ℕ}

noncomputable instance (N h : ℕ) : Fintype (Construction N h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ h ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h)))

/-- The single edge at every depth. -/
def leaf (h : ℕ) : Construction N h :=
  match h with
  | 0 => ()
  | _+1 => .inl ()

/-- The newly closed chain at a prescribed arity. -/
def node (h : ℕ) (j : nonlinearDegrees N) (w : Fin j.val → Construction N h) :
    Construction N (h+1) := .inr ⟨j,w⟩

lemma arity_ge_two (j : nonlinearDegrees N) : 2 ≤ j.val :=
  (mem_nonlinearDegrees.mp j.property).1

lemma chain_ofFn_nonempty (j : nonlinearDegrees N) (w : Fin j.val → BasicShape) :
    List.ofFn w ≠ [] := by
  intro he
  have h := congrArg List.length he
  simp only [List.length_ofFn,List.length_nil] at h
  have hj := arity_ge_two j
  omega

/-- The canonical basic shape of a construction tree. -/
def shape (N : ℕ) : (h : ℕ) → Construction N h → BasicShape
  | 0,_ => singleEdgeShape
  | _+1,.inl _ => singleEdgeShape
  | h+1,.inr ⟨j,w⟩ =>
    Chain.close (List.ofFn (fun i ↦ shape N h (w i))) (chain_ofFn_nonempty j _)

@[simp]
lemma shape_leaf (h : ℕ) : shape N h (leaf h) = singleEdgeShape := by
  cases h <;> rfl

lemma shape_node (h : ℕ) (j : nonlinearDegrees N) (w : Fin j.val → Construction N h) :
    shape N (h+1) (node h j w) =
      Chain.close (List.ofFn (fun i ↦ shape N h (w i))) (chain_ofFn_nonempty j _) := rfl

private lemma span_ge_length (C : Chain) : C.length ≤ Chain.span C := by
  induction C with
  | nil => rfl
  | cons T C ih =>
    have h := T.span_pos
    simp only [List.length_cons,Chain.span_cons]
    omega

private lemma node_size_pos (h : ℕ) (j : nonlinearDegrees N) (w : Fin j.val → Construction N h) :
    0 < (shape N (h+1) (node h j w)).additionalVertices := by
  let C := List.ofFn (fun i ↦ shape N h (w i))
  have h := span_ge_length C
  have hC : C.length = j.val := List.length_ofFn
  have hj := arity_ge_two j
  change 0 < Chain.span C-1
  omega

/-- Each constructed shape has a unique ordered construction at a fixed depth. -/
theorem shape_injective (N h : ℕ) : Function.Injective (shape N h) := by
  induction h with
  | zero => exact fun _ _ _ ↦ Subsingleton.elim _ _
  | succ h ih =>
    intro x y he
    change Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h) at x y
    rcases x with (x | ⟨j,x⟩) <;> rcases y with (y | ⟨k,y⟩)
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · have hPos := node_size_pos h k y
      change singleEdgeShape = shape N (h+1) (node h k y) at he
      rw [← he] at hPos
      exact (Nat.lt_irrefl 0 hPos).elim
    · have hPos := node_size_pos h j x
      change shape N (h+1) (node h j x) = singleEdgeShape at he
      rw [he] at hPos
      exact (Nat.lt_irrefl 0 hPos).elim
    · change shape N (h+1) (node h j x) = shape N (h+1) (node h k y) at he
      rw [shape_node,shape_node] at he
      have hLj : 2 ≤ (List.ofFn (fun i ↦ shape N h (x i))).length := by rw [List.length_ofFn]; exact arity_ge_two j
      have hLk : 2 ≤ (List.ofFn (fun i ↦ shape N h (y i))).length := by rw [List.length_ofFn]; exact arity_ge_two k
      have hL := Chain.close_injective hLj hLk _ _ he
      have hEq : j = k := Subtype.ext (by
        have h := congrArg List.length hL
        simpa only [List.length_ofFn] using h)
      subst k
      have hWord := List.ofFn_injective hL
      have hw : x = y := funext fun i ↦ ih (congrFun hWord i)
      subst y
      rfl

/-- The unnormalized coefficient inherited from the root and its constituents. -/
noncomputable def coefficient (N : ℕ) : (h : ℕ) → Construction N h → ℝ
  | 0,_ => singleEdgeCoefficient N
  | _+1,.inl _ => singleEdgeCoefficient N
  | h+1,.inr ⟨j,w⟩ => bernsteinCoefficient N j.val * ∏ i, coefficient N h (w i)

@[simp]
lemma coefficient_leaf (h : ℕ) : coefficient N h (leaf h) = singleEdgeCoefficient N := by
  cases h <;> rfl

lemma coefficient_node (h : ℕ) (j : nonlinearDegrees N) (w : Fin j.val → Construction N h) :
    coefficient N (h+1) (node h j w) = bernsteinCoefficient N j.val * ∏ i, coefficient N h (w i) := rfl

/-- The squared norm of all coefficients at one depth. -/
noncomputable def mass (N h : ℕ) : ℝ := ∑ t : Construction N h, (coefficient N h t)^2

lemma mass_pos {N : ℕ} (hN : 0 < N) (h : ℕ) : 0 < mass N h := by
  unfold mass
  have he := single_le_sum (f := fun t : Construction N h ↦ (coefficient N h t)^2)
    (fun t _ ↦ sq_nonneg (coefficient N h t)) (mem_univ (leaf h))
  rw [coefficient_leaf] at he
  exact (pow_pos (singleEdgeCoefficient_pos hN) _).trans_le he

lemma mass_succ (N h : ℕ) :
    mass N (h+1) = singleEdgeCoefficient N ^ 2 +
      ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j ^ 2 * (mass N h)^j := by
  unfold mass
  change (∑ t : Unit ⊕ (Σ j : nonlinearDegrees N, Fin j.val → Construction N h),
    (coefficient N (h+1) t)^2) = _
  rw [Fintype.sum_sum_type]
  have hSigma : (∑ t : (Σ j : nonlinearDegrees N, Fin j.val → Construction N h),
      (coefficient N (h+1) (.inr t))^2) =
      ∑ j : nonlinearDegrees N, ∑ w : Fin j.val → Construction N h,
        (coefficient N (h+1) (node h j w))^2 := by
    calc
      _ = ∑ t : (Σ j : nonlinearDegrees N, Fin j.val → Construction N h),
          (coefficient N (h+1) (node h t.1 t.2))^2 := sum_congr rfl fun t _ ↦ by cases t; rfl
      _ = _ := Fintype.sum_sigma' (fun (j : nonlinearDegrees N) (w : Fin j.val → Construction N h) ↦
        (coefficient N (h+1) (node h j w))^2)
  rw [hSigma]
  have hWord (j : nonlinearDegrees N) : (∑ w : Fin j.val → Construction N h,
      (coefficient N (h+1) (node h j w))^2) =
      bernsteinCoefficient N j.val^2 * (∑ t : Construction N h, (coefficient N h t)^2)^j.val := by
    simp_rw [coefficient_node,mul_pow,← prod_pow,← mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun (_i : Fin j.val) (t : Construction N h) ↦ (coefficient N h t)^2),
      prod_const,card_univ,Fintype.card_fin]
  simp_rw [hWord]
  rw [sum_coe_sort (nonlinearDegrees N) (fun j : ℕ ↦ bernsteinCoefficient N j^2 *
    (∑ t : Construction N h, (coefficient N h t)^2)^j)]
  simp [coefficient]

lemma mass_eq_depthWeight {N : ℕ} (hN : 0 < N) (h : ℕ) :
    mass N h = depthWeight (nonlinearDegrees N) (bernsteinCoefficient N) h := by
  have hA : singleEdgeCoefficient N^2 = edgeWeight (nonlinearDegrees N) (bernsteinCoefficient N) :=
    Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 5/8).trans
      (edgeWeight_ge (fun _ hj ↦ (mem_nonlinearDegrees.mp hj).1) (bernsteinCoefficient_energy hN)))
  induction h with
  | zero =>
    unfold mass
    change (∑ t : Unit, (coefficient N 0 t)^2) = _
    simpa only [Fintype.sum_unique,coefficient,depthWeight] using hA
  | succ h ih => rw [mass_succ,hA,ih,depthWeight]

lemma mass_le_one {N : ℕ} (hN : 0 < N) (h : ℕ) : mass N h ≤ 1 := by
  rw [mass_eq_depthWeight hN]
  exact (depthWeight_mem_interval
    ((by norm_num : (0 : ℝ) ≤ 5/8).trans (edgeWeight_ge (fun _ hj ↦ (mem_nonlinearDegrees.mp hj).1)
      (bernsteinCoefficient_energy hN))) h).2

/-- The coefficient norm approaches one as the depth is increased. -/
theorem tendsto_mass {N : ℕ} (hN : 0 < N) : Tendsto (mass N) atTop (𝓝 1) := by
  let a := edgeWeight (nonlinearDegrees N) (bernsteinCoefficient N)
  have hA : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 5/8).trans
    (edgeWeight_ge (fun _ hj ↦ (mem_nonlinearDegrees.mp hj).1) (bernsteinCoefficient_energy hN))
  have ht : Tendsto (fun h : ℕ ↦ 1-(3/4 : ℝ)^h*(1-a)) atTop (𝓝 1) := by
    have he := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
      (by norm_num : (3/4 : ℝ) < 1)).mul_const (1-a)
    simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds
  · apply Eventually.of_forall
    intro h
    have he := one_sub_depthWeight_le hA (bernsteinCoefficient_energy hN) h
    rw [mass_eq_depthWeight hN]
    linarith
  · exact Eventually.of_forall (mass_le_one hN)

/-- The coefficients at a fixed depth, normalized to squared norm one. -/
noncomputable def normalized (N h : ℕ) (t : Construction N h) : ℝ :=
  coefficient N h t / Real.sqrt (mass N h)

lemma sum_sq_normalized {N : ℕ} (hN : 0 < N) (h : ℕ) :
    (∑ t : Construction N h, (normalized N h t)^2) = 1 := by
  simp only [normalized,div_pow,← sum_div,Real.sq_sqrt (mass_pos hN h).le]
  exact div_self (mass_pos hN h).ne'

end Construction

end LovaszTheta.Independent
