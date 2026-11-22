module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic

/-!
# The primal Lovász theta program

The variables are real matrices. Positive semidefiniteness includes symmetry.
The objective and feasible set are those in equation (1) of the manuscript.
-/

@[expose] public section

open Matrix Finset
open scoped Matrix

namespace LovaszTheta

variable {V : Type*} [Fintype V]

/-- The all-ones matrix. -/
def allOnes : Matrix V V ℝ := fun _ _ ↦ 1

/-- Entrywise pairing of real matrices. -/
def pairing (A B : Matrix V V ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- The objective of the primal semidefinite program. -/
def objective (X : Matrix V V ℝ) : ℝ := ∑ i, ∑ j, X i j

/-- The feasible matrices in the semidefinite definition of theta. -/
def Feasible (G : SimpleGraph V) (X : Matrix V V ℝ) : Prop :=
  X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0

/-- The Lovász theta number as the supremum of the primal objective values. -/
noncomputable def theta (G : SimpleGraph V) : ℝ :=
  sSup (objective '' {X | Feasible G X})

lemma objective_eq_pairing (X : Matrix V V ℝ) : objective X = pairing allOnes X := by
  simp [objective, pairing, allOnes]

lemma pairing_add_left (A B X : Matrix V V ℝ) :
    pairing (A + B) X = pairing A X + pairing B X := by
  simp [pairing, add_mul, sum_add_distrib]

lemma pairing_sub_left (A B X : Matrix V V ℝ) :
    pairing (A - B) X = pairing A X - pairing B X := by
  simp [pairing, sub_mul, sum_sub_distrib]

lemma pairing_smul_left (r : ℝ) (A X : Matrix V V ℝ) :
    pairing (r • A) X = r * pairing A X := by
  simp [pairing, mul_assoc, mul_sum]

lemma pairing_one [DecidableEq V] (X : Matrix V V ℝ) : pairing 1 X = X.trace := by
  simp [pairing, Matrix.one_apply, Matrix.trace, ite_mul]

lemma pairing_vecMulVec (A : Matrix V V ℝ) (x : V → ℝ) :
    pairing A (vecMulVec x x) = x ⬝ᵥ (A *ᵥ x) := by
  simp only [pairing, vecMulVec_apply, dotProduct, Matrix.mulVec, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

lemma objective_nonneg {X : Matrix V V ℝ} (hX : X.PosSemidef) : 0 ≤ objective X := by
  simpa [objective, Matrix.mulVec, dotProduct] using
    hX.dotProduct_mulVec_nonneg (fun _ ↦ (1 : ℝ))

lemma pairing_nonneg {A B : Matrix V V ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ pairing A B :=
  objective_nonneg (hA.hadamard hB)

lemma objective_add (A B : Matrix V V ℝ) :
    objective (A + B) = objective A + objective B := by
  simp [objective, sum_add_distrib]

lemma objective_smul (r : ℝ) (X : Matrix V V ℝ) :
    objective (r • X) = r * objective X := by
  simp [objective, mul_sum]

lemma objective_allOnes : objective (allOnes : Matrix V V ℝ) = (Fintype.card V : ℝ) ^ 2 := by
  simp [objective, allOnes, pow_two]

lemma objective_one [DecidableEq V] : objective (1 : Matrix V V ℝ) = Fintype.card V := by
  simp [objective, Matrix.one_apply]

lemma posSemidef_allOnes : (allOnes : Matrix V V ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [allOnes]
  · intro x
    simpa [allOnes, Matrix.mulVec, dotProduct, sum_mul, pow_two] using sq_nonneg (∑ i, x i)

lemma posSemidef_card_smul_one_sub_allOnes [DecidableEq V] :
    ((Fintype.card V : ℝ) • (1 : Matrix V V ℝ) - allOnes).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact (Matrix.isHermitian_one.smul (by simp)).sub posSemidef_allOnes.isHermitian
  · intro x
    rw [star_trivial, ← pairing_vecMulVec, pairing_sub_left, pairing_smul_left, pairing_one,
      ← objective_eq_pairing]
    have h := sq_sum_le_card_mul_sum_sq (s := univ) (f := x)
    simpa [Matrix.trace, objective, vecMulVec_apply, ← mul_sum, ← sum_mul, pow_two] using
      sub_nonneg.mpr h

lemma objective_le_card {G : SimpleGraph V} {X : Matrix V V ℝ} (hX : Feasible G X) :
    objective X ≤ Fintype.card V := by
  classical
  have h := pairing_nonneg (posSemidef_card_smul_one_sub_allOnes (V := V)) hX.1
  rwa [pairing_sub_left, pairing_smul_left, pairing_one, hX.2.1, mul_one,
    ← objective_eq_pairing, sub_nonneg] at h

lemma feasible_scaled_identity [Nonempty V] [DecidableEq V] (G : SimpleGraph V) :
    Feasible G ((Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ)) := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨Matrix.PosSemidef.one.smul (by positivity), ?_, ?_⟩
  · simp [Matrix.trace_one, hc]
  · intro i j hij
    simp [hij.ne]

lemma theta_values_nonempty [Nonempty V] (G : SimpleGraph V) :
    (objective '' {X | Feasible G X}).Nonempty := by
  classical
  exact ⟨_, _, feasible_scaled_identity G, rfl⟩

lemma theta_values_bddAbove (G : SimpleGraph V) :
    BddAbove (objective '' {X | Feasible G X}) :=
  ⟨Fintype.card V, by rintro _ ⟨X, hX, rfl⟩; exact objective_le_card hX⟩

lemma objective_le_theta {G : SimpleGraph V} {X : Matrix V V ℝ} (hX : Feasible G X) :
    objective X ≤ theta G :=
  le_csSup (theta_values_bddAbove G) ⟨X, hX, rfl⟩

lemma theta_le [Nonempty V] {G : SimpleGraph V} {b : ℝ}
    (h : ∀ X, Feasible G X → objective X ≤ b) : theta G ≤ b :=
  csSup_le (theta_values_nonempty G) (by rintro _ ⟨X, hX, rfl⟩; exact h X hX)

lemma one_le_theta [Nonempty V] (G : SimpleGraph V) : 1 ≤ theta G := by
  classical
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa [objective_smul, objective_one, hc] using objective_le_theta (feasible_scaled_identity G)

lemma theta_le_card [Nonempty V] (G : SimpleGraph V) : theta G ≤ Fintype.card V :=
  theta_le fun _ ↦ objective_le_card

/-- A spectral majorant for a matrix that agrees with the objective on free entries. -/
theorem theta_le_of_majorant [Nonempty V] [DecidableEq V] {G : SimpleGraph V}
    {B : Matrix V V ℝ} {c : ℝ} (hPsd : (c • (1 : Matrix V V ℝ) - B).PosSemidef)
    (hB : ∀ i j, ¬G.Adj i j → B i j = 1) : theta G ≤ c := by
  classical
  refine theta_le fun X hX ↦ ?_
  have hBX : pairing B X = objective X := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · simp [hX.2.2 i j hij]
    · simp [hB i j hij]
  have h := pairing_nonneg hPsd hX.1
  rwa [pairing_sub_left, pairing_smul_left, pairing_one, hX.2.1, mul_one, hBX, sub_nonneg] at h

/-- Equation (2), the upper bound from a positive semidefinite witness. -/
theorem theta_le_of_witness [Nonempty V] {G : SimpleGraph V} {W : Matrix V V ℝ}
    {a b : ℝ} (ha : 0 < a) (hW : W.PosSemidef) (hdiag : ∀ i, W i i = b)
    (hnonedge : ∀ i j, i ≠ j → ¬G.Adj i j → W i j = -a / Real.sqrt (Fintype.card V)) :
    theta G ≤ 1 + (b / a) * Real.sqrt (Fintype.card V) := by
  classical
  let s := Real.sqrt (Fintype.card V)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  let B : Matrix V V ℝ := (1 + b / a * s) • (1 : Matrix V V ℝ) - (s / a) • W
  have hB : ∀ i j, ¬G.Adj i j → B i j = 1 := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      simp only [B, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
        mul_one, hdiag]
      ring
    · simp only [B, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne heq,
        mul_zero, hnonedge i j heq hij]
      change 0 - s / a * (-a / s) = 1
      field_simp
      ring
  apply theta_le_of_majorant (B := B) _ hB
  change ((1 + b / a * s) • (1 : Matrix V V ℝ) - B).PosSemidef
  dsimp only [B]
  rw [sub_sub_cancel]
  exact hW.smul (div_nonneg hs.le ha.le)

end LovaszTheta
