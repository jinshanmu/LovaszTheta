module

public import LovaszTheta.Duality
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Finite Fourier analysis for the circulant program

The unnormalized Fourier matrix uses the negative-exponent convention in
the manuscript. Its diagonalization of a real even circulant gives the
eigenvalues and positivity condition of the Fourier linear program.
-/

@[expose] public section

open Finset Matrix
open scoped ComplexOrder Matrix ZMod

namespace LovaszTheta.Circulant

variable {n : ℕ} [NeZero n]

/-- The unnormalized discrete Fourier matrix. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun k j ↦ ZMod.stdAddChar (-(k * j))

lemma star_stdAddChar (a : ZMod n) : star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

lemma fourierMatrix_conjTranspose_apply (i j : ZMod n) :
    (fourierMatrix n)ᴴ i j = ZMod.stdAddChar (i * j) := by
  rw [conjTranspose_apply, fourierMatrix, star_stdAddChar, neg_neg, mul_comm]

lemma sum_stdAddChar_mul (a : ZMod n) :
    (∑ j, ZMod.stdAddChar (a * j)) = if a = 0 then (n : ℂ) else 0 := by
  by_cases h : a = 0
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

lemma fourierMatrix_mul_conjTranspose :
    fourierMatrix n * (fourierMatrix n)ᴴ = (n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  ext i k
  simp only [Matrix.mul_apply, fourierMatrix_conjTranspose_apply]
  change (∑ j, ZMod.stdAddChar (-(i * j)) * ZMod.stdAddChar (j * k)) = _
  simp_rw [← AddChar.map_add_eq_mul, mul_comm _ k, ← neg_mul, ← add_mul]
  rw [sum_stdAddChar_mul]
  by_cases hik : i = k
  · simp [hik]
  · have hk : -i + k ≠ 0 := by rwa [neg_add_eq_sub, sub_ne_zero, ne_comm]
    simp [hik, hk]

lemma fourierMatrix_conjTranspose_mul :
    (fourierMatrix n)ᴴ * fourierMatrix n = (n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  ext i k
  simp only [Matrix.mul_apply, fourierMatrix_conjTranspose_apply]
  change (∑ j, ZMod.stdAddChar (i * j) * ZMod.stdAddChar (-(j * k))) = _
  simp_rw [← AddChar.map_add_eq_mul, mul_comm _ k, ← neg_mul, ← add_mul]
  rw [sum_stdAddChar_mul]
  by_cases hik : i = k
  · simp [hik]
  · have hk : i + -k ≠ 0 := by rwa [← sub_eq_add_neg, sub_ne_zero]
    simp [hik, hk]

lemma fourierMatrix_mulVec (x : ZMod n → ℂ) : fourierMatrix n *ᵥ x = 𝓕 x := by
  funext k
  simp only [Matrix.mulVec, dotProduct, fourierMatrix, ZMod.dft_apply, smul_eq_mul, mul_comm k]

lemma fourierMatrix_conjTranspose_mulVec (x : ZMod n → ℂ) :
    (fourierMatrix n)ᴴ *ᵥ x = (n : ℂ) • 𝓕⁻ x := by
  funext k
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp only [Matrix.mulVec, dotProduct, fourierMatrix_conjTranspose_apply, Pi.smul_apply,
    ZMod.invDFT_apply, smul_eq_mul, mul_comm k, ← mul_assoc (n : ℂ), mul_inv_cancel₀ hn, one_mul]

/-- The Fourier multiplier with a given complex symbol on the residue side. -/
noncomputable def multiplier (a : ZMod n → ℂ) : Matrix (ZMod n) (ZMod n) ℂ :=
  (n : ℂ)⁻¹ • (fourierMatrix n * Matrix.diagonal a * (fourierMatrix n)ᴴ)

lemma multiplier_mul (a b : ZMod n → ℂ) :
    multiplier a * multiplier b = multiplier (fun i ↦ a i * b i) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hProd :
      (fourierMatrix n * diagonal a * (fourierMatrix n)ᴴ) *
        (fourierMatrix n * diagonal b * (fourierMatrix n)ᴴ) =
      (n : ℂ) • (fourierMatrix n * diagonal (fun i ↦ a i * b i) *
        (fourierMatrix n)ᴴ) := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (fourierMatrix n)ᴴ,
      fourierMatrix_conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
      ← Matrix.mul_assoc (diagonal a), Matrix.diagonal_mul_diagonal]
  unfold multiplier
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hProd, smul_smul,
    mul_assoc ((n : ℂ)⁻¹), inv_mul_cancel₀ hn, mul_one]

/-- The real-to-complex map on matrices preserves and reflects positive semidefiniteness. -/
lemma posSemidef_map_ofReal_iff {V : Type*} [Fintype V] [DecidableEq V] {X : Matrix V V ℝ} :
    (X.map Complex.ofReal).PosSemidef ↔ X.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      have hij := h.isHermitian.apply i j
      simpa using hij
    · intro x
      rw [star_trivial]
      have hx := h.dotProduct_mulVec_nonneg (fun i ↦ (x i : ℂ))
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Matrix.mulVec, dotProduct,
        Matrix.map_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sum] at hx
      exact Complex.zero_le_real.mp hx
  · intro h
    open scoped MatrixOrder in
    let B := CFC.sqrt X
    have hB := (CFC.sqrt_nonneg X).posSemidef
    have hSq : Bᴴ * B = X := by
      rw [hB.isHermitian.eq, ← pow_two, CFC.sq_sqrt X h.nonneg]
    have hm : (B.map Complex.ofReal)ᴴ = Bᴴ.map Complex.ofReal := by
      ext i j
      simp
    rw [← hSq]
    change ((Bᴴ * B).map Complex.ofRealHom).PosSemidef
    rw [Matrix.map_mul]
    change ((Bᴴ.map Complex.ofReal) * B.map Complex.ofReal).PosSemidef
    rw [← hm]
    exact Matrix.posSemidef_conjTranspose_mul_self _

lemma circulant_invDFT (x : ZMod n → ℂ) :
    Matrix.circulant (𝓕⁻ x) =
      (n : ℂ)⁻¹ • ((fourierMatrix n)ᴴ * diagonal x * fourierMatrix n) := by
  ext i j
  rw [Matrix.circulant_apply, ZMod.invDFT_apply, Matrix.smul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,
    fourierMatrix_conjTranspose_apply, smul_eq_mul]
  congr 1
  exact sum_congr rfl fun k _ ↦ by
    change ZMod.stdAddChar (k * (i - j)) * x k =
      (ZMod.stdAddChar (i * k) * x k) * ZMod.stdAddChar (-(k * j))
    rw [mul_sub, AddChar.map_sub_eq_div, mul_comm i, AddChar.map_neg_eq_inv]
    ring

lemma dft_ofReal_eq_ofReal_re {x : ZMod n → ℝ} (hx : x.Even) (k : ZMod n) :
    ((𝓕 (fun i ↦ (x i : ℂ)) k).re : ℂ) = 𝓕 (fun i ↦ (x i : ℂ)) k := by
  let y := 𝓕 (fun i ↦ (x i : ℂ))
  have hy : y.Even := ZMod.dft_even_iff.mpr fun i ↦ congrArg Complex.ofReal (hx i)
  have hStar : star (y k) = y (-k) := by
    simp only [y, ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, star_stdAddChar, neg_neg,
      mul_neg, Complex.star_def, Complex.conj_ofReal]
    congr 1
    ext i
    ring
  rw [hy k] at hStar
  apply Complex.ext
  · simp
  · have hIm := congrArg Complex.im hStar
    simp only [Complex.star_def, Complex.conj_im] at hIm
    simp only [Complex.ofReal_im]
    linarith

lemma circulant_psd_iff_dft_nonneg {x : ZMod n → ℝ} (hx : x.Even) :
    (Matrix.circulant x).PosSemidef ↔ ∀ k, 0 ≤ (𝓕 (fun j ↦ (x j : ℂ)) k).re := by
  let y := 𝓕 (fun j ↦ (x j : ℂ))
  have hyreal (k : ZMod n) : ((y k).re : ℂ) = y k := dft_ofReal_eq_ofReal_re hx k
  have hD : (Matrix.circulant x).map Complex.ofReal =
      (n : ℂ)⁻¹ • ((fourierMatrix n)ᴴ * diagonal y * fourierMatrix n) := by
    rw [Matrix.map_circulant, ← circulant_invDFT]
    change Matrix.circulant (fun j ↦ (x j : ℂ)) = Matrix.circulant (𝓕⁻ y)
    rw [LinearEquiv.symm_apply_apply]
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hinv : 0 ≤ (n : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      Complex.zero_le_real.mpr (inv_nonneg.mpr hn.le)
  rw [← posSemidef_map_ofReal_iff, hD]
  constructor
  · intro h k
    have h' := h.mul_mul_conjTranspose_same (fourierMatrix n)
    have hM : fourierMatrix n *
        ((n : ℂ)⁻¹ • ((fourierMatrix n)ᴴ * diagonal y * fourierMatrix n)) *
        (fourierMatrix n)ᴴ = (n : ℂ) • diagonal y := by
      calc
        _ = (n : ℂ)⁻¹ • ((fourierMatrix n * (fourierMatrix n)ᴴ) *
            diagonal y * (fourierMatrix n * (fourierMatrix n)ᴴ)) := by
              simp [Matrix.mul_assoc]
        _ = _ := by
          have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
          rw [fourierMatrix_mul_conjTranspose]
          simp [smul_smul, hnz]
    rw [hM] at h'
    have h'' := h'.smul hinv
    have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [smul_smul, inv_mul_cancel₀ hnz, one_smul] at h''
    have hDiag := Matrix.posSemidef_diagonal_iff.mp h'' k
    rwa [← hyreal k, Complex.zero_le_real] at hDiag
  · intro h
    have hy : (diagonal y).PosSemidef := Matrix.PosSemidef.diagonal fun k ↦ by
      change 0 ≤ y k
      rw [← hyreal k, Complex.zero_le_real]
      exact h k
    exact (hy.conjTranspose_mul_mul_same (fourierMatrix n)).smul hinv

end LovaszTheta.Circulant
