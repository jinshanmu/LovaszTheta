module

public import LovaszTheta.Barrier
public import LovaszTheta.Fourier
public import LovaszTheta.RandomGraphs

/-!
# The circulant Fourier program

Averaging the primal matrix over translations gives a circulant.
Fourier diagonalization identifies its possible spectra with even
probability vectors in the kernel of the connection-set projection.
-/

@[expose] public section

open Finset Matrix
open scoped ComplexOrder Matrix ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The connection residues of a sample of the circulant model. -/
def connectionSet (x : InversionClass n → Bool) : Set (ZMod n) :=
  {s | epsilon x s = -1}

/-- Projection on the span of Fourier modes with residues in a prescribed set. -/
noncomputable def fourierProjection (S : Set (ZMod n)) : Matrix (ZMod n) (ZMod n) ℂ := by
  classical
  exact multiplier fun s ↦ if s ∈ S then 1 else 0

lemma fourierProjection_mulVec_eq_zero_iff (S : Set (ZMod n)) (y : ZMod n → ℂ) :
    fourierProjection S *ᵥ y = 0 ↔ ∀ s ∈ S, ((fourierMatrix n)ᴴ *ᵥ y) s = 0 := by
  classical
  let z := (fourierMatrix n)ᴴ *ᵥ y
  let a : ZMod n → ℂ := fun s ↦ if s ∈ S then 1 else 0
  have hVec : fourierProjection S *ᵥ y = (n : ℂ)⁻¹ • 𝓕 (fun s ↦ a s * z s) := by
    unfold fourierProjection multiplier
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      fourierMatrix_mulVec]
    congr 2
    funext s
    exact Matrix.mulVec_diagonal _ _ _
  rw [hVec, smul_eq_zero, or_iff_right (inv_ne_zero (by exact_mod_cast NeZero.ne n)),
    ← map_zero (ZMod.dft : (ZMod n → ℂ) ≃ₗ[ℂ] _), ZMod.dft.injective.eq_iff]
  constructor
  · intro h s hs
    simpa [a, hs] using congrFun h s
  · intro h
    funext s
    by_cases hs : s ∈ S
    · simp only [a, ite_eq_left hs, one_mul]
      change z s = 0
      exact h s hs
    · simp [a, hs]

/-- An even probability vector satisfying the Fourier edge constraints. -/
def FourierFeasible (x : InversionClass n → Bool) (y : ZMod n → ℝ) : Prop :=
  y.Even ∧ (∀ k, 0 ≤ y k) ∧ mass y = 1 ∧
    fourierProjection (connectionSet x) *ᵥ (fun k ↦ (y k : ℂ)) = 0

private def translate (a : ZMod n) (X : Matrix (ZMod n) (ZMod n) ℝ) :
    Matrix (ZMod n) (ZMod n) ℝ :=
  X.submatrix (· + a) (· + a)

private lemma translate_trace (a : ZMod n) (X : Matrix (ZMod n) (ZMod n) ℝ) :
    (translate a X).trace = X.trace :=
  Equiv.sum_comp (Equiv.addRight a) (fun i ↦ X i i)

private lemma translate_objective (a : ZMod n) (X : Matrix (ZMod n) (ZMod n) ℝ) :
    objective (translate a X) = objective X := by
  unfold objective
  calc
    _ = ∑ i, ∑ j, X (i + a) j :=
      sum_congr rfl fun i _ ↦ Equiv.sum_comp (Equiv.addRight a) (X (i + a))
    _ = _ := Equiv.sum_comp (Equiv.addRight a) (fun i ↦ ∑ j, X i j)

private noncomputable def translationAverage (X : Matrix (ZMod n) (ZMod n) ℝ) :
    Matrix (ZMod n) (ZMod n) ℝ :=
  (n : ℝ)⁻¹ • ∑ a, translate a X

private lemma translationAverage_feasible (x : InversionClass n → Bool)
    {X : Matrix (ZMod n) (ZMod n) ℝ} (hX : Feasible (graph x) X) :
    Feasible (graph x) (translationAverage X) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hPsd : (∑ a, translate a X).PosSemidef :=
    (Matrix.PosSemidef.addSubmonoid (ZMod n) ℝ).sum_mem
      (fun a _ ↦ hX.1.submatrix (· + a))
  refine ⟨hPsd.smul (by positivity), ?_, ?_⟩
  · simp [translationAverage, trace_sum, translate_trace, hX.2.1, ZMod.card, hn]
  · intro i j hij
    simp only [translationAverage, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    have hZero (a : ZMod n) : translate a X i j = 0 := by
      apply hX.2.2
      simpa only [graph_adj_iff_epsilon, add_sub_add_right_eq_sub] using hij
    simp [hZero]

private lemma translationAverage_objective (X : Matrix (ZMod n) (ZMod n) ℝ) :
    objective (translationAverage X) = objective X := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hsum : objective (∑ a, translate a X) = ∑ a, objective (translate a X) := by
    simp only [objective, Matrix.sum_apply]
    calc
      (∑ i, ∑ j, ∑ a, translate a X i j) = ∑ i, ∑ a, ∑ j, translate a X i j :=
        sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [translationAverage, objective_smul, hsum, translate_objective, sum_const,
    card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

private lemma translationAverage_circulant (X : Matrix (ZMod n) (ZMod n) ℝ) :
    translationAverage X = Matrix.circulant (fun s ↦ translationAverage X s 0) := by
  ext i j
  simp only [Matrix.circulant_apply, translationAverage, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, translate, Matrix.submatrix_apply, zero_add]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight j) _ _ fun a ↦ by
    simp [sub_eq_add_neg, add_left_comm, add_comm]

private lemma circulant_trace (z : ZMod n → ℝ) :
    (Matrix.circulant z).trace = (n : ℝ) * z 0 := by
  simp [Matrix.trace, Matrix.circulant_apply, ZMod.card]

private lemma circulant_objective (z : ZMod n → ℝ) :
    objective (Matrix.circulant z) = (n : ℝ) * mass z := by
  unfold objective
  have h (i : ZMod n) : (∑ j, z (i - j)) = mass z := by
    exact Fintype.sum_equiv ((Equiv.neg (ZMod n)).trans (Equiv.addLeft i)) _ _ fun j ↦
      congrArg z (sub_eq_add_neg i j)
  simp only [Matrix.circulant_apply, h, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

private lemma fourierMatrix_conjTranspose_mulVec_zero (z : ZMod n → ℂ) :
    ((fourierMatrix n)ᴴ *ᵥ z) 0 = ∑ k, z k := by
  simp only [Matrix.mulVec, dotProduct, fourierMatrix_conjTranspose_apply, zero_mul,
    AddChar.map_zero_eq_one, one_mul]

private lemma ofReal_idft_re {y : ZMod n → ℝ} (hy : y.Even) (k : ZMod n) :
    ((𝓕⁻ (fun j ↦ (y j : ℂ)) k).re : ℂ) = 𝓕⁻ (fun j ↦ (y j : ℂ)) k := by
  have hY := dft_ofReal_eq_ofReal_re hy (-k)
  have hVal : 𝓕⁻ (fun j ↦ (y j : ℂ)) k =
      ((n : ℝ)⁻¹ * (𝓕 (fun j ↦ (y j : ℂ)) (-k)).re : ℝ) := by
    rw [ZMod.invDFT_apply', smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, hY]
  rw [hVal, Complex.ofReal_re]

private lemma circulant_of_fourierFeasible (x : InversionClass n → Bool) {y : ZMod n → ℝ}
    (hy : FourierFeasible x y) :
    ∃ X, Feasible (graph x) X ∧ objective X = (n : ℝ) * y 0 := by
  let z : ZMod n → ℝ := fun s ↦ (𝓕⁻ (fun k ↦ (y k : ℂ)) s).re
  have hzOf : (fun s ↦ (z s : ℂ)) = 𝓕⁻ (fun k ↦ (y k : ℂ)) :=
    funext (ofReal_idft_re hy.1)
  have hzEven : z.Even := by
    intro s
    have hYEven : (𝓕 (fun k ↦ (y k : ℂ))).Even :=
      ZMod.dft_even_iff.mpr (fun k ↦ congrArg Complex.ofReal (hy.1 k))
    simp only [z, ZMod.invDFT_apply', neg_neg, hYEven s]
  have hzDft : 𝓕 (fun s ↦ (z s : ℂ)) = fun k ↦ (y k : ℂ) := by rw [hzOf, LinearEquiv.apply_symm_apply]
  have hInv : (fourierMatrix n)ᴴ *ᵥ (fun k ↦ (y k : ℂ)) = (n : ℂ) • (fun s ↦ (z s : ℂ)) := by
    rw [fourierMatrix_conjTranspose_mulVec, hzOf]
  have hMass : mass z = y 0 := by
    have h0 := congrFun hzDft 0
    rw [ZMod.dft_apply_zero, ← Complex.ofReal_sum] at h0
    exact Complex.ofReal_injective h0
  refine ⟨Matrix.circulant z, ⟨(circulant_psd_iff_dft_nonneg hzEven).mpr ?_, ?_, ?_⟩, ?_⟩
  · simpa only [hzDft, Complex.ofReal_re] using hy.2.1
  · rw [circulant_trace]
    have h0 := congrFun hInv 0
    rw [fourierMatrix_conjTranspose_mulVec_zero, ← Complex.ofReal_sum] at h0
    change ((mass y : ℝ) : ℂ) = (n : ℂ) * (z 0 : ℂ) at h0
    exact Complex.ofReal_injective (by simpa only [hy.2.2.1, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_one] using h0.symm)
  · intro i j hij
    have hz := (fourierProjection_mulVec_eq_zero_iff _ _).mp hy.2.2.2 (i - j)
      (graph_adj_iff_epsilon x i j |>.mp hij)
    rw [hInv] at hz
    change (n : ℂ) * (z (i - j) : ℂ) = 0 at hz
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  · rw [circulant_objective, hMass]

private lemma exists_fourierFeasible_of_feasible (x : InversionClass n → Bool)
    {X : Matrix (ZMod n) (ZMod n) ℝ} (hX : Feasible (graph x) X) :
    ∃ y, FourierFeasible x y ∧ (n : ℝ) * y 0 = objective X := by
  let z : ZMod n → ℝ := fun s ↦ translationAverage X s 0
  have hC : translationAverage X = Matrix.circulant z := translationAverage_circulant X
  have hZ : Feasible (graph x) (Matrix.circulant z) := hC ▸ translationAverage_feasible x hX
  have hzEven : z.Even := by
    intro s
    have h := hZ.1.isHermitian.apply s 0
    simpa [Matrix.circulant_apply, zero_sub] using h
  let y : ZMod n → ℝ := fun k ↦ (𝓕 (fun s ↦ (z s : ℂ)) k).re
  have hDFT : (fun k ↦ (y k : ℂ)) = 𝓕 (fun s ↦ (z s : ℂ)) :=
    funext (dft_ofReal_eq_ofReal_re hzEven)
  have hInv : (fourierMatrix n)ᴴ *ᵥ (fun k ↦ (y k : ℂ)) = (n : ℂ) • (fun s ↦ (z s : ℂ)) := by
    rw [fourierMatrix_conjTranspose_mulVec, hDFT, LinearEquiv.symm_apply_apply]
  have hyNonneg : ∀ k, 0 ≤ y k := (circulant_psd_iff_dft_nonneg hzEven).mp hZ.1
  have hyEven : y.Even := fun k ↦ congrArg Complex.re
    ((ZMod.dft_even_iff.mpr fun s ↦ congrArg Complex.ofReal (hzEven s)) k)
  have hMassEq : mass y = (n : ℝ) * z 0 := by
    have h0 := congrFun hInv 0
    rw [fourierMatrix_conjTranspose_mulVec_zero, ← Complex.ofReal_sum] at h0
    exact Complex.ofReal_injective (by simpa only [mass, Complex.ofReal_mul, Complex.ofReal_natCast,
      Pi.smul_apply, smul_eq_mul] using h0)
  have hMass : mass y = 1 := by
    rw [hMassEq, ← circulant_trace]
    exact hZ.2.1
  have hProj : fourierProjection (connectionSet x) *ᵥ (fun k ↦ (y k : ℂ)) = 0 := by
    rw [fourierProjection_mulVec_eq_zero_iff, hInv]
    intro s hs
    have hAdj : (graph x).Adj s 0 := by
      rw [graph_adj_iff_epsilon, sub_zero]
      exact hs
    have hz : z s = 0 := by simpa [Matrix.circulant_apply] using hZ.2.2 s 0 hAdj
    simp [hz]
  refine ⟨y, ⟨hyEven, hyNonneg, hMass, hProj⟩, ?_⟩
  have hY0 : y 0 = mass z := by
    have h0 := congrFun hDFT 0
    rw [ZMod.dft_apply_zero, ← Complex.ofReal_sum] at h0
    exact Complex.ofReal_injective h0
  rw [hY0, ← circulant_objective, ← hC, translationAverage_objective]

/-- The value of the Fourier program equals the semidefinite theta number. -/
theorem theta_isMax_fourier (x : InversionClass n → Bool) :
    ∃ y, FourierFeasible x y ∧ (n : ℝ) * y 0 = theta (graph x) ∧
      ∀ q, FourierFeasible x q → (n : ℝ) * q 0 ≤ (n : ℝ) * y 0 := by
  obtain ⟨X, hX, hopt⟩ := exists_theta_maximizer (graph x)
  obtain ⟨y, hy, hyObj⟩ := exists_fourierFeasible_of_feasible x hX
  refine ⟨y, hy, hyObj.trans hopt, fun q hq ↦ ?_⟩
  obtain ⟨Q, hQ, hQobj⟩ := circulant_of_fourierFeasible x hq
  rw [← hQobj, hyObj, hopt]
  exact objective_le_theta hQ

end LovaszTheta.Circulant
