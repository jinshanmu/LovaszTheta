module

public import LovaszTheta.CertificatePolynomial
public import LovaszTheta.RoughNorm
public import Mathlib.Data.Matrix.Basic

/-!
# Positivity from a nearby matrix polynomial

A polynomial that is nearly nonnegative on the spectral interval
remains positive after an identity shift that also absorbs the
operator-norm error. Symmetrizing the candidate preserves the
entry constraints and cannot increase that error.
-/

@[expose] public section

open Matrix Polynomial Unitary
open scoped Classical Matrix Matrix.Norms.L2Operator Polynomial

namespace LovaszTheta.Independent

/-- The symmetric part of a real square matrix. -/
noncomputable def symmetricPart {V : Type*} (A : Matrix V V ℝ) : Matrix V V ℝ :=
  (1/2 : ℝ) • (A + Aᵀ)

lemma symmetricPart_isSymm {V : Type*} (A : Matrix V V ℝ) : (symmetricPart A).IsSymm := by
  change (symmetricPart A)ᵀ = symmetricPart A
  rw [symmetricPart,transpose_smul,transpose_add,transpose_transpose,add_comm]

private lemma norm_symmetricPart_le {V : Type*} [Fintype V] (A : Matrix V V ℝ) :
    ‖symmetricPart A‖ ≤ ‖A‖ := by
  have ht : ‖Aᵀ‖ = ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial,l2_opNorm_conjTranspose]
  rw [symmetricPart,norm_smul,Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
  calc
    _ ≤ (1/2 : ℝ)*(‖A‖+‖Aᵀ‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [ht]; ring

private lemma aeval_diagonal {V : Type*} [Fintype V] [DecidableEq V] (v : V → ℝ) (p : ℝ[X]) :
    aeval (diagonal v) p = diagonal (fun i ↦ p.eval (v i)) := by
  let f : (V → ℝ) →ₐ[ℝ] Matrix V V ℝ := Matrix.diagonalAlgHom ℝ
  calc
    _ = f (aeval v p) := Polynomial.aeval_algHom_apply f v p
    _ = _ := by
      change diagonal (aeval v p) = _
      apply congrArg diagonal
      funext i
      rw [Polynomial.aeval_pi_apply₂,Polynomial.coe_aeval_eq_eval]

private lemma shifted_polynomial_psd {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (p : ℝ[X]) (b : ℝ)
    (h : ∀ i, 0 ≤ p.eval (hA.eigenvalues i)+b) :
    (aeval A p + b • (1 : Matrix V V ℝ)).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let v := hA.eigenvalues
  let f := conjStarAlgAut ℝ _ U
  have hA' : A = f (diagonal v) := hA.spectral_theorem
  have hP : aeval A p = f (diagonal (fun i ↦ p.eval (v i))) := by
    rw [hA',aeval_algHom_apply,aeval_diagonal]
  have hDiag : diagonal (fun _ : V ↦ b) = b • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases he : i = j <;> simp [he]
  have hI : b • (1 : Matrix V V ℝ) = f (diagonal (fun _ ↦ b)) := by
    rw [hDiag,map_smul,map_one]
  have hAdd : (diagonal (fun i ↦ p.eval (v i)) + diagonal (fun _ ↦ b) : Matrix V V ℝ) =
      diagonal (fun i ↦ p.eval (v i)+b) := diagonal_add _ _
  rw [hP,hI,← map_add,hAdd]
  have hD : (diagonal (fun i ↦ p.eval (v i)+b)).PosSemidef :=
    posSemidef_diagonal_iff.mpr h
  change (conjStarAlgAut ℝ _ U (diagonal (fun i ↦ p.eval (v i)+b))).PosSemidef
  rw [conjStarAlgAut_apply,← Unitary.coe_star]
  exact hD.mul_mul_conjTranspose_same (↑U : Matrix V V ℝ)

private lemma abs_eigenvalue_le_norm {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : V) : |hA.eigenvalues i| ≤ ‖A‖ := by
  let U := hA.eigenvectorUnitary
  let v := hA.eigenvalues
  have hD : A = conjStarAlgAut ℝ _ U (diagonal v) := hA.spectral_theorem
  have hN : ‖A‖ = ‖v‖ := by
    rw [hD,conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal]
  rw [hN,← Real.norm_eq_abs]
  exact norm_le_pi_norm _ _

private lemma matrix_isHermitian_of_isSymm {V : Type*} {A : Matrix V V ℝ} (h : A.IsSymm) :
    A.IsHermitian := by
  change Aᴴ = A
  rw [conjTranspose_eq_transpose_of_trivial]
  exact h

/-- A small enlargement of the semicircle interval lowers the certificate
polynomial by an arbitrarily small amount. -/
theorem certificatePolynomial_near_interval {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc (-2-δ) (2+δ), -a ≤ (certificatePolynomial N).eval x := by
  let F := (certificatePolynomial N).eval
  have hC : Continuous F := (certificatePolynomial N).continuous
  obtain ⟨d₁,h₁,hL⟩ := Metric.continuousAt_iff.mp (hC.continuousAt (x := (-2 : ℝ))) a ha
  obtain ⟨d₂,h₂,hR⟩ := Metric.continuousAt_iff.mp (hC.continuousAt (x := (2 : ℝ))) a ha
  let δ := min d₁ d₂/2
  have hd : 0 < δ := div_pos (lt_min h₁ h₂) (by norm_num)
  refine ⟨δ,hd,?_⟩
  intro x hx
  have hδ₁ : δ < d₁ := (half_lt_self (lt_min h₁ h₂)).trans_le (min_le_left _ _)
  have hδ₂ : δ < d₂ := (half_lt_self (lt_min h₁ h₂)).trans_le (min_le_right _ _)
  by_cases hLower : x < -2
  · have hv : dist x (-2) < d₁ := by
      rw [Real.dist_eq,abs_of_nonpos (by linarith)]
      linarith [hx.1]
    have hc := hL hv
    rw [Real.dist_eq,abs_lt] at hc
    have hf := certificatePolynomial_nonneg hN (show (-2 : ℝ) ∈ Set.Icc (-2) 2 by norm_num)
    exact (by linarith [hc.1] : -a ≤ F x)
  by_cases hUpper : 2 < x
  · have hv : dist x 2 < d₂ := by
      rw [Real.dist_eq,abs_of_nonneg (by linarith)]
      linarith [hx.2]
    have hc := hR hv
    rw [Real.dist_eq,abs_lt] at hc
    have hf := certificatePolynomial_nonneg hN (show (2 : ℝ) ∈ Set.Icc (-2) 2 by norm_num)
    exact (by linarith [hc.1] : -a ≤ F x)
  · exact (neg_nonpos.mpr ha.le).trans (certificatePolynomial_nonneg hN ⟨by linarith,by linarith⟩)

/-- An identity shift absorbs the spectral lower bound and the operator-norm error. -/
theorem posSemidef_symmetricPart_add_of_near_polynomial {V : Type*} [Fintype V] [DecidableEq V]
    {A W : Matrix V V ℝ} (hA : A.IsSymm) (p : ℝ[X]) {R a b : ℝ}
    (hR : ‖A‖ ≤ R) (hp : ∀ x ∈ Set.Icc (-R) R, -a ≤ p.eval x)
    (hW : ‖W - aeval A p‖ ≤ b) :
    (symmetricPart W + (a+b) • (1 : Matrix V V ℝ)).PosSemidef := by
  let F := aeval A p
  let E := symmetricPart W-F
  have hAh := matrix_isHermitian_of_isSymm hA
  have hF : (F + a • (1 : Matrix V V ℝ)).PosSemidef := shifted_polynomial_psd A hAh p a fun i ↦ by
    have hEigen := (abs_eigenvalue_le_norm hAh i).trans hR
    have h' := hp _ (abs_le.mp hEigen)
    linarith
  have hFt : Fᵀ = F := by
    have he := hF.isHermitian.eq
    rw [conjTranspose_eq_transpose_of_trivial,transpose_add,transpose_smul,transpose_one] at he
    exact add_right_cancel he
  have hE : E.IsSymm := by
    change (symmetricPart W-F)ᵀ = _
    rw [transpose_sub,symmetricPart_isSymm W,hFt]
  have hEs : E = symmetricPart (W-F) := by
    unfold E symmetricPart
    rw [transpose_sub,hFt]
    module
  have hENorm : ‖E‖ ≤ b := by rw [hEs]; exact (norm_symmetricPart_le _).trans hW
  have hEp : (E + b • (1 : Matrix V V ℝ)).PosSemidef := by
    have h := shifted_polynomial_psd E (matrix_isHermitian_of_isSymm hE) X b (fun i ↦ by
      rw [eval_X]
      have hEigen := (abs_eigenvalue_le_norm (matrix_isHermitian_of_isSymm hE) i).trans hENorm
      linarith [(abs_le.mp hEigen).1])
    rwa [aeval_X] at h
  have heq : (F+a • (1 : Matrix V V ℝ))+(E+b • (1 : Matrix V V ℝ)) =
      symmetricPart W+(a+b) • (1 : Matrix V V ℝ) := by
    unfold E
    rw [add_smul]
    abel
  exact heq ▸ hF.add hEp

end LovaszTheta.Independent
