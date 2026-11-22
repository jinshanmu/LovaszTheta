module

public import LovaszTheta.EqualityPatterns
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The rough graph-matrix norm bound

Color averaging and Jensen reduce the graph-matrix moment to the
colored trace moment. The count of equality patterns bounds that
moment. Taking a moment of order twice the ceiling of the logarithm
gives the polynomial failure probability in the manuscript.
-/

@[expose] public section

open Finset Matrix Unitary
open scoped Classical Matrix Matrix.Norms.L2Operator

namespace LovaszTheta.Independent

lemma opNorm_pow_le_trace {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix V V ℝ) (k : ℕ) :
    ‖A‖ ^ (2*k) ≤ ((A * Aᵀ) ^ k).trace := by
  let B := A * Aᴴ
  have hB : B.PosSemidef := posSemidef_self_mul_conjTranspose A
  let U := hB.isHermitian.eigenvectorUnitary
  let v := hB.isHermitian.eigenvalues
  have hv (i : V) : 0 ≤ v i := hB.eigenvalues_nonneg i
  have hDiag : B = conjStarAlgAut ℝ _ U (diagonal v) := by
    exact hB.isHermitian.spectral_theorem
  have hNorm : ‖B‖ = ‖v‖ := by
    rw [hDiag, conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  have hNormSq : ‖B‖ = ‖A‖ ^ 2 := by
    unfold B
    simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using
      l2_opNorm_conjTranspose_mul_self Aᴴ
  have hTrace : (B ^ k).trace = ∑ i, v i ^ k := by
    rw [hDiag, ← map_pow, diagonal_pow, conjStarAlgAut_apply, trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, trace_diagonal]
    rfl
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
  have hAt : ‖v‖ = v i := hi.symm.trans (Real.norm_of_nonneg (hv i))
  rw [← conjTranspose_eq_transpose_of_trivial, pow_mul, ← hNormSq, hNorm, hAt]
  change v i ^ k ≤ (B ^ k).trace
  rw [hTrace]
  exact single_le_sum (fun j _ ↦ pow_nonneg (hv j) _) (mem_univ i)

private lemma opNorm_average_pow_le {Ω V : Type*} [Fintype Ω] [Nonempty Ω] [Fintype V]
    (A : Ω → Matrix V V ℝ) (p : ℕ) :
    ‖(Fintype.card Ω : ℝ)⁻¹ • (∑ w, A w)‖ ^ p ≤ average (fun w ↦ ‖A w‖ ^ p) := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let a := (Fintype.card Ω : ℝ)⁻¹
  have ha : 0 ≤ a := by positivity
  have hNorm : ‖a • (∑ w, A w)‖ ≤ ∑ w, a * ‖A w‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) ha
  have hJ := (convexOn_pow (𝕜 := ℝ) p).map_sum_le (t := (univ : Finset Ω))
    (w := fun _ ↦ a) (p := fun w ↦ ‖A w‖) (fun _ _ ↦ ha)
    (by simp [a, hc]) (fun _ _ ↦ norm_nonneg _)
  have hAvg : (∑ w, a * ‖A w‖ ^ p) = average (fun w ↦ ‖A w‖ ^ p) := by
    rw [← mul_sum, average, div_eq_inv_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hNorm _).trans (by
    simpa only [smul_eq_mul, hAvg] using hJ)

private lemma average_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (f : Ω → Λ → ℝ) :
    average (fun x ↦ average (f x)) = average (fun y ↦ average (fun x ↦ f x y)) := by
  simp only [average, ← sum_div, div_div]
  rw [sum_comm, mul_comm]

/-- The (2k)-th moment used in the rough bound. -/
theorem average_opNorm_graphMatrix_pow_le {V : Type*} [Fintype V] [Nonempty V]
    (α : Shape) {k : ℕ} (hk : 0 < k) :
    average (fun x : EdgeIndex V → Bool ↦ ‖graphMatrix α x‖ ^ (2*k)) ≤
      (α.vertexCount : ℝ) ^ (2*k*α.vertexCount) *
        (2*k*α.vertexCount : ℝ) ^ (2*k*α.vertexCount) *
        (Fintype.card V : ℝ) ^ α.traceLabelBound k := by
  let Col := V → Fin α.vertexCount
  let : Nonempty (Fin α.vertexCount) := ⟨α.left⟩
  have hV : 0 < (α.vertexCount : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt α.left.isLt)
  let c := (α.vertexCount : ℝ) ^ α.vertexCount
  have hc : 0 < c := pow_pos hV _
  let moment (x : EdgeIndex V → Bool) (color : Col) :=
    let A := coloredGraphMatrix α x color
    ((A * Aᵀ) ^ k).trace
  have hCol (x : EdgeIndex V → Bool) :
      (Fintype.card Col : ℝ)⁻¹ • (∑ color : Col, coloredGraphMatrix α x color) =
        c⁻¹ • graphMatrix α x := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, ← div_eq_inv_mul]
    exact (average_coloredGraphMatrix α x i j).trans (by simp only [c, inv_pow, div_eq_inv_mul])
  have hPoint (x : EdgeIndex V → Bool) : ‖graphMatrix α x‖ ^ (2*k) ≤
      c ^ (2*k) * average (moment x) := by
    have h := opNorm_average_pow_le (fun color : Col ↦ coloredGraphMatrix α x color) (2*k)
    rw [hCol x, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), mul_pow, inv_pow] at h
    have hCancel : (c ^ (2*k)) * ((c ^ (2*k))⁻¹ * ‖graphMatrix α x‖ ^ (2*k)) =
        ‖graphMatrix α x‖ ^ (2*k) := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc.ne'), one_mul]
    rw [← hCancel]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le _)
    exact h.trans (average_mono fun color ↦ opNorm_pow_le_trace (coloredGraphMatrix α x color) k)
  have hCount (color : Col) :
      average (fun x ↦ moment x color) ≤
        (2*k*α.vertexCount : ℝ) ^ (2*k*α.vertexCount) *
          (Fintype.card V : ℝ) ^ α.traceLabelBound k := by
    have he : average (fun x ↦ moment x color) = Fintype.card (ColoredTrace α k color) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact average_trace_coloredGraphMatrix_pow α color j
    rw [he]
    exact_mod_cast card_coloredTrace_le α hk color
  calc
    _ ≤ average (fun x ↦ c ^ (2*k) * average (moment x)) := average_mono hPoint
    _ = c ^ (2*k) * average (fun color ↦ average (fun x ↦ moment x color)) := by
      rw [average_mul_left, average_comm moment]
    _ ≤ c ^ (2*k) * ((2*k*α.vertexCount : ℝ) ^ (2*k*α.vertexCount) *
          (Fintype.card V : ℝ) ^ α.traceLabelBound k) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le _)
      exact (average_mono hCount).trans_eq (average_const _)
    _ = _ := by
      dsimp only [c]
      rw [← pow_mul, Nat.mul_comm α.vertexCount (2*k), ← mul_assoc]

/-- The rough separator estimate in the independent-edge proof with an
explicit constant and failure probability. -/
theorem probability_opNorm_graphMatrix_gt {V : Type*} [Fintype V] (α : Shape)
    (hn : 3 ≤ Fintype.card V) {m : ℝ} (hm : 0 ≤ m) :
    let n := Fintype.card V
    probability (fun x : EdgeIndex V → Bool ↦
      (4 * (α.vertexCount : ℝ)^2) ^ α.vertexCount * Real.log n ^ α.vertexCount *
        Real.exp ((m+1)/2) *
        (n : ℝ) ^ ((↑(α.vertexCount + α.isolatedInterior.card - α.boundaryIndicator) : ℝ) / 2)
      < ‖graphMatrix α x‖) ≤ (n : ℝ) ^ (-m) := by
  let n := Fintype.card V
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v := α.vertexCount
  let ι := α.boundaryIndicator
  let d := v + α.isolatedInterior.card - ι
  let k := ⌈Real.log (n : ℝ)⌉₊
  let c := (2*(k : ℝ)*(v : ℝ)^2)^v
  let T := c * Real.exp ((m+1)/2) * (n : ℝ) ^ ((d : ℝ)/2)
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hv : 0 < (v : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt α.left.isLt
  have hLog : 1 ≤ Real.log (n : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_three])
  have hk : 0 < k := Nat.one_le_ceil_iff.mpr (by linarith)
  have hkUp : (k : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ Real.log (n : ℝ) by linarith)
    change (k : ℝ) < Real.log n + 1 at h
    linarith
  have hT : 0 < T := by
    dsimp [T, c]
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hTle : T ≤
      (4 * (v : ℝ)^2)^v * Real.log n ^ v * Real.exp ((m+1)/2) *
        (n : ℝ) ^ ((d : ℝ)/2) := by
    dsimp [T, c]
    rw [← mul_pow]
    have hBase : 2 * (k : ℝ) * (v : ℝ)^2 ≤ (4 * (v : ℝ)^2) * Real.log n := by
      nlinarith only [mul_le_mul_of_nonneg_right hkUp (sq_nonneg (v : ℝ))]
    have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (k : ℝ) * (v : ℝ)^2) hBase v
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPow (Real.exp_pos _).le) (by positivity)
  have hK : Real.log (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hι : ι ≤ 1 := by unfold ι Shape.boundaryIndicator; split_ifs <;> norm_num
  have hRatio : (n : ℝ)^ι ≤ (n : ℝ)^(-m) * Real.exp ((m+1)*k) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnPos, Real.rpow_def_of_pos hnPos,
      ← Real.exp_add, Real.exp_le_exp]
    have hOne : (ι : ℝ) ≤ 1 := by exact_mod_cast hι
    have hI := mul_le_mul_of_nonneg_left hOne (show 0 ≤ Real.log (n : ℝ) by linarith)
    have hE := mul_le_mul_of_nonneg_left hK (show 0 ≤ m+1 by linarith)
    linarith
  have hcPow : c ^ (2*k) = (v : ℝ)^(2*k*v) * (2*k*v : ℝ) ^ (2*k*v) := by
    unfold c
    rw [← pow_mul, Nat.mul_comm v, ← mul_pow]
    congr 1
    ring
  have hNPow : ((n : ℝ)^((d : ℝ)/2))^(2*k) = (n : ℝ)^(k*d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnPos.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hEPow : (Real.exp ((m+1)/2))^(2*k) = Real.exp ((m+1)*k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  let Z := average (fun x : EdgeIndex V → Bool ↦ ‖graphMatrix α x‖^(2*k))
  have hMoment := average_opNorm_graphMatrix_pow_le (V := V) α hk
  change Z ≤ (v : ℝ)^(2*k*v) * (2*k*v : ℝ)^(2*k*v) * (n : ℝ)^(k*d+ι) at hMoment
  have hMom : Z ≤ (n : ℝ)^(-m) * T^(2*k) := by
    have hFactor : (v : ℝ)^(2*k*v) * (2*k*v : ℝ)^(2*k*v) * (n : ℝ)^(k*d+ι) =
        (c^(2*k) * (n : ℝ)^(k*d)) * (n : ℝ)^ι := by
      rw [pow_add, ← hcPow, ← mul_assoc]
    calc
      Z ≤ (c^(2*k) * (n : ℝ)^(k*d)) * (n : ℝ)^ι := hMoment.trans_eq hFactor
      _ ≤ (c^(2*k) * (n : ℝ)^(k*d)) * ((n : ℝ)^(-m) * Real.exp ((m+1)*k)) :=
        mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ = _ := by
        dsimp only [T]
        rw [mul_pow, mul_pow, hNPow, hEPow]
        ring
  calc
    _ ≤ probability (fun x : EdgeIndex V → Bool ↦
        T^(2*k) ≤ ‖graphMatrix α x‖^(2*k)) := probability_mono fun x hx ↦
      pow_le_pow_left₀ hT.le (hTle.trans hx.le) _
    _ ≤ Z / T^(2*k) := probability_le_average_div _ (pow_pos hT _) (fun _ ↦ by positivity)
    _ ≤ _ := (div_le_iff₀ (pow_pos hT _)).mpr hMom

end LovaszTheta.Independent
