module

public import LovaszTheta.ClosureCoefficients
public import LovaszTheta.ChainChebyshev
public import LovaszTheta.SpectralCertificate

/-!
# The witness for the independent-edge graph

The nonlinear summands vanish on nonedges after the entrywise
closure is added. Their boundaries are distinct, so they also have
zero diagonal. The polynomial approximation gives positivity
after the prescribed identity shift.
-/

@[expose] public section

open Finset Filter Matrix Polynomial LovaszTheta
open scoped Classical Matrix Matrix.Norms.L2Operator Polynomial Topology

namespace LovaszTheta.Independent

/-- The unshifted matrix assembled from the single edge and the chain terms. -/
noncomputable def witnessCandidate (N h : ℕ) (D : ℕ → MatrixFamily) : MatrixFamily :=
  bernsteinCoefficient N 0 • (1 : MatrixFamily) +
    Construction.normalized N h (Construction.leaf h) • blockFamily singleEdgeShape +
      ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j •
        ((Construction.chains N h j + D j) + closeEntries (Construction.chains N h j + D j))

private lemma chainSum_diag {J : Type*} [Fintype J] (α : J → BasicShape) (c : J → ℝ)
    {j : ℕ} (hj : 0 < j) (n : ℕ) (x : SignSample n) (i : Fin n) :
    chainSum α c j n x i i = 0 := by
  simp only [chainSum,Finset.sum_apply,Pi.smul_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply sum_eq_zero
  intro w _
  have he : wordChain α w ≠ [] := by
    intro h
    have hL := congrArg List.length h
    simp only [wordChain,List.length_ofFn,List.length_nil] at hL
    omega
  rw [chainFamily_diag_of_ne_empty _ he,mul_zero]

private lemma closeEntries_apply (A : MatrixFamily) (n : ℕ) (x : SignSample n) (i j : Fin n) :
    closeEntries A n x i j = signedAdjacency x i j * A n x i j := rfl

private lemma witnessCandidate_diag (N h : ℕ) (D : ℕ → MatrixFamily)
    (hD : ∀ j ∈ nonlinearDegrees N, D j ∈ pairSpace) (n : ℕ) (x : SignSample n) (i : Fin n) :
    witnessCandidate N h D n x i i = bernsteinCoefficient N 0 := by
  have hSum :
      (∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j •
        ((Construction.chains N h j + D j) + closeEntries (Construction.chains N h j + D j))) n x i i = 0 := by
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,
      closeEntries_apply,signedAdjacency_diag,zero_mul,add_zero]
    apply sum_eq_zero
    intro j hj
    have hJ : 0 < j := by have := (mem_nonlinearDegrees.mp hj).1; omega
    rw [Construction.chains,chainSum_diag _ _ hJ,pairSpace_diag_zero (hD j hj),add_zero,mul_zero]
  unfold witnessCandidate
  rw [Pi.add_apply,Pi.add_apply,Pi.add_apply,Pi.add_apply,Matrix.add_apply,Matrix.add_apply,hSum,add_zero,
    Pi.smul_apply,Pi.smul_apply,Matrix.smul_apply,Pi.smul_apply,Pi.smul_apply,blockFamily_singleEdge,
    Matrix.smul_apply,Matrix.smul_apply,signedAdjacency_diag,smul_zero,smul_zero,add_zero]
  change bernsteinCoefficient N 0 * ((1 : Matrix (Fin n) (Fin n) ℝ) i i) = _
  rw [Matrix.one_apply_eq,mul_one]

private lemma witnessCandidate_nonedge (N h : ℕ) (D : ℕ → MatrixFamily)
    (n : ℕ) (x : SignSample n) (i j : Fin n) (hij : i ≠ j) (hG : ¬(graph x).Adj i j) :
    witnessCandidate N h D n x i j = -Construction.normalized N h (Construction.leaf h) / Real.sqrt n := by
  have hSign := signedAdjacency_nonedge x hij hG
  have hSum :
      (∑ k ∈ nonlinearDegrees N, bernsteinCoefficient N k •
        ((Construction.chains N h k + D k) + closeEntries (Construction.chains N h k + D k))) n x i j = 0 := by
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,
      closeEntries_apply,hSign,neg_one_mul,add_neg_cancel,mul_zero,sum_const_zero]
  unfold witnessCandidate
  rw [Pi.add_apply,Pi.add_apply,Pi.add_apply,Pi.add_apply,Matrix.add_apply,Matrix.add_apply,hSum,add_zero,
    Pi.smul_apply,Pi.smul_apply,Matrix.smul_apply,Pi.smul_apply,Pi.smul_apply,blockFamily_singleEdge,
    Matrix.smul_apply,Matrix.smul_apply,hSign]
  change bernsteinCoefficient N 0 * ((1 : Matrix (Fin n) (Fin n) ℝ) i j) +
    Construction.normalized N h (Construction.leaf h)*(1/Real.sqrt (n : ℝ)*(-1)) = _
  rw [Matrix.one_apply_ne hij]
  ring

private lemma certificate_evaluation (N h : ℕ) (hN : 0 < N) (D E : ℕ → MatrixFamily)
    (hEval : ∀ j, polynomialFamily (Construction.combination N h) (semicircleChebyshev j) =
      Construction.chains N h j + D j + E j) :
    polynomialFamily (Construction.combination N h) (certificatePolynomial N) =
      bernsteinCoefficient N 0 • (1 : MatrixFamily) + Construction.combination N h +
        ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j • (Construction.chains N h j + D j + E j) := by
  funext n x
  unfold polynomialFamily
  rw [certificatePolynomial_expansion hN,map_add,map_add,map_sum,semicircleChebyshev_one,aeval_X,aeval_C]
  simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,Finset.sum_apply]
  rw [Algebra.algebraMap_eq_smul_one]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [map_mul,aeval_C,Algebra.algebraMap_eq_smul_one,Matrix.smul_mul,one_mul]
  exact congrArg (fun K : MatrixFamily ↦ bernsteinCoefficient N j • K n x) (hEval j)

private lemma witnessCandidate_error (N h : ℕ) (hN : 0 < N) (D E : ℕ → MatrixFamily)
    (hEval : ∀ j, polynomialFamily (Construction.combination N h) (semicircleChebyshev j) =
      Construction.chains N h j + D j + E j) :
    witnessCandidate N h D - polynomialFamily (Construction.combination N h) (certificatePolynomial N) =
      blockCombination (Construction.shape N (h+1)) (Construction.difference N h) +
        ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j • (closeEntries (D j)-E j) := by
  rw [witnessCandidate,certificate_evaluation N h hN D E hEval,Construction.blockCombination_difference]
  simp only [map_add,smul_add,smul_sub,sum_add_distrib,sum_sub_distrib]
  abel

private lemma witnessCandidate_shift_theta_bound (N h : ℕ) (D : ℕ → MatrixFamily)
    (hD : ∀ j ∈ nonlinearDegrees N, D j ∈ pairSpace) (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    {n : ℕ} (hn : 0 < n) (x : SignSample n)
    (hPSD : (symmetricPart (witnessCandidate N h D n x) + η • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hb : 0 ≤ bernsteinCoefficient N 0) :
    theta (graph x) ≤ 1+((bernsteinCoefficient N 0+η)/singleEdgeCoefficient N)*Real.sqrt n := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let W := witnessCandidate N h D n x
  let a := Construction.normalized N h (Construction.leaf h)
  let b := bernsteinCoefficient N 0+η
  have ha : a = singleEdgeCoefficient N/Real.sqrt (Construction.mass N h) := by
    simp only [a,Construction.normalized,Construction.coefficient_leaf]
  have hA : 0 < a := by
    rw [ha]
    exact div_pos (singleEdgeCoefficient_pos hN) (Real.sqrt_pos.mpr (Construction.mass_pos hN h))
  have hDiag i : (symmetricPart W + η • (1 : Matrix (Fin n) (Fin n) ℝ)) i i = b := by
    simp only [symmetricPart,Matrix.add_apply,Matrix.smul_apply,Matrix.transpose_apply,smul_eq_mul,
      Matrix.one_apply_eq,mul_one,W,witnessCandidate_diag N h D hD,b]
    ring
  have hNon i j (hij : i ≠ j) (hG : ¬(graph x).Adj i j) :
      (symmetricPart W + η • (1 : Matrix (Fin n) (Fin n) ℝ)) i j =
        -a / Real.sqrt ↑(Fintype.card (Fin n)) := by
    simp only [symmetricPart,Matrix.add_apply,Matrix.smul_apply,Matrix.transpose_apply,smul_eq_mul,
      Matrix.one_apply_ne hij,mul_zero,add_zero,Fintype.card_fin,W,
      witnessCandidate_nonedge N h D n x i j hij hG,
      witnessCandidate_nonedge N h D n x j i hij.symm (fun he ↦ hG he.symm),a]
    ring
  have hBound := theta_le_of_witness hA hPSD hDiag hNon
  rw [Fintype.card_fin] at hBound
  refine hBound.trans ?_
  have hs : Real.sqrt (Construction.mass N h) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (Construction.mass_le_one hN h)
  have hb' : 0 ≤ b/singleEdgeCoefficient N :=
    div_nonneg (add_nonneg hb hη.le) (singleEdgeCoefficient_pos hN).le
  have he : b/a = (b/singleEdgeCoefficient N)*Real.sqrt (Construction.mass N h) := by rw [ha,div_div_eq_mul_div,mul_div_right_comm]
  rw [he]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hb' hs) (Real.sqrt_nonneg _))

/-- The manuscript's independent-edge upper bound holds with each fixed inverse-power failure rate. -/
theorem withHighProbability_theta_le (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    (hb : 0 ≤ bernsteinCoefficient N 0) :
    WithHighProbability (fun n x ↦
      theta (graph x) ≤ 1+((bernsteinCoefficient N 0+η)/singleEdgeCoefficient N)*Real.sqrt n) := by
  obtain ⟨h,hh⟩ := ((Construction.tendsto_differenceNorm hN).eventually_lt_const
    (show (0 : ℝ) < η/9 by positivity)).exists
  let α := Construction.shape N h
  let c := Construction.normalized N h
  let r := Construction.reversal N h
  have hα := Construction.shape_injective N h
  have hs (j : Construction N h) : α (r j) = (α j).reverse := Construction.shape_reverse N h j
  have hr (j : Construction N h) : c (r j) = c j := Construction.normalized_reverse N h j
  have hc := Construction.sum_sq_normalized hN h
  have hDecomp (j : ℕ) := exists_chebyshev_decomposition α c hα r hs hr hc j
  choose D hD E hE hEval using hDecomp
  obtain ⟨δ,hδ,hSpec⟩ := certificatePolynomial_near_interval hN (show (0 : ℝ) < η/3 by positivity)
  have hM : WithHighProbability (fun n x ↦ ‖Construction.combination N h n x‖ ≤ 2+δ) := by
    simpa only [Construction.combination,α,c,hc,Real.sqrt_one,mul_one] using
      withHighProbability_blockCombination α c hα r hs hr hδ
  let diff := blockCombination (Construction.shape N (h+1)) (Construction.difference N h)
  have hDiff : WithHighProbability (fun n x ↦ ‖diff n x‖ ≤ η/3) := by
    have he := withHighProbability_blockCombination (Construction.shape N (h+1)) (Construction.difference N h)
      (Construction.shape_injective N (h+1)) (Construction.reversal N (h+1))
      (Construction.shape_reverse N (h+1)) (Construction.difference_reverse N h) (by norm_num : (0 : ℝ) < 1)
    exact he.mono fun n x hx ↦ hx.trans (by linarith)
  let tail := ∑ j ∈ nonlinearDegrees N, bernsteinCoefficient N j • (closeEntries (D j)-E j)
  have hTail : NormVanishes tail := by
    have he := NormVanishes.sum (nonlinearDegrees N)
      (fun j ↦ bernsteinCoefficient N j • (closeEntries (D j)-E j))
      (fun j _ ↦ ((normVanishes_close_pairSpace (hD j)).sub (hE j)).smul _)
    refine he.congr (Eventually.of_forall fun n x ↦ ?_)
    simp only [tail,Finset.sum_apply]
  have hNonempty : WithHighProbability (fun n _ ↦ 0 < n) :=
    WithHighProbability.of_eventually ((eventually_ge_atTop (1 : ℕ)).mono fun _ hn _ ↦ by omega)
  apply ((hM.and hDiff).and ((hTail (η/3) (by positivity)).and hNonempty)).mono
  intro n x hx
  have hPoly : ‖witnessCandidate N h D n x - aeval (Construction.combination N h n x)
      (certificatePolynomial N)‖ ≤ 2*η/3 := by
    have he := congrArg (fun K : MatrixFamily ↦ K n x) (witnessCandidate_error N h hN D E hEval)
    change witnessCandidate N h D n x - aeval (Construction.combination N h n x)
      (certificatePolynomial N) = diff n x + tail n x at he
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hx.1.2,hx.2.1])
  have hhSym := blockCombination_isSymm α c r hs hr n x
  have hp := posSemidef_symmetricPart_add_of_near_polynomial hhSym (certificatePolynomial N)
    hx.1.1 (a := η/3) (b := 2*η/3)
    (fun y hy ↦ hSpec y ⟨by linarith [hy.1],hy.2⟩) hPoly
  rw [show η/3+2*η/3 = η by ring] at hp
  exact witnessCandidate_shift_theta_bound N h D (fun j _ ↦ hD j) hN hη hx.2.2 x hp hb

end LovaszTheta.Independent
