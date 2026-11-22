module

public import LovaszTheta.Theta
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Sequences

/-!
# Semidefinite duality and graph complementation

The trace-one positive semidefinite matrices form a compact convex set. Separating the
image under the edge constraints and objective from a point above the optimum gives
positive semidefinite certificates. A compactness argument attains the dual optimum.
-/

@[expose] public section

open Matrix Finset Set Filter
open scoped Topology Matrix

namespace LovaszTheta

variable {V : Type*} [Fintype V]

lemma continuous_objective : Continuous (objective (V := V)) := by
  unfold objective
  fun_prop

lemma continuous_trace : Continuous (Matrix.trace (R := ℝ) (n := V)) := by
  unfold Matrix.trace Matrix.diag
  fun_prop

/-- Each entry of a positive semidefinite matrix has magnitude at most its trace. -/
lemma abs_apply_le_trace {X : Matrix V V ℝ} (hX : X.PosSemidef) (i j : V) :
    |X i j| ≤ X.trace := by
  have hdiag (k : V) : X k k ≤ X.trace :=
    Finset.single_le_sum (f := fun k ↦ X k k) (fun k _ ↦ hX.diag_nonneg) (mem_univ k)
  have hsym : X j i = X i j := by simpa using hX.isHermitian.apply i j
  let e : Fin 2 → V := ![i, j]
  have hPlus := (hX.submatrix e).dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  have hMinus := (hX.submatrix e).dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  simp [e, Fin.sum_univ_two, Matrix.mulVec, dotProduct, hsym] at hPlus hMinus
  exact abs_le.mpr ⟨by linarith [hdiag i, hdiag j], by linarith [hdiag i, hdiag j]⟩

private lemma isClosed_psd_trace (t : ℝ) :
    IsClosed {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = t} :=
  (isClosed_setOfPred_posSemidef (n := V) (R := ℝ)).inter (isClosed_eq continuous_trace continuous_const)

private lemma isCompact_psd_trace (t : ℝ) :
    IsCompact {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = t} := by
  have hBox : IsCompact (Set.pi univ (fun _ : V ↦ Set.pi univ (fun _ : V ↦ Icc (-t) t))) :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  refine hBox.of_isClosed_subset (isClosed_psd_trace t) fun X hX i _ j _ ↦ ?_
  exact abs_le.mp ((abs_apply_le_trace hX.1 i j).trans_eq hX.2)

private lemma convex_psd_trace (t : ℝ) :
    Convex ℝ {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = t} := by
  intro X hX Y hY a b ha hb hab
  change X.PosSemidef ∧ X.trace = t at hX
  change Y.PosSemidef ∧ Y.trace = t at hY
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb), ?_⟩
  rw [trace_add, trace_smul, trace_smul, hX.2, hY.2, smul_eq_mul, smul_eq_mul, ← add_mul, hab,
    one_mul]

private noncomputable def edgePart (G : SimpleGraph V) (X : Matrix V V ℝ) : Matrix V V ℝ := by
  classical
  exact fun i j ↦ if G.Adj i j then X i j else 0

omit [Fintype V] in
private lemma edgePart_eq_zero_iff {G : SimpleGraph V} {X : Matrix V V ℝ} :
    edgePart G X = 0 ↔ ∀ i j, G.Adj i j → X i j = 0 := by
  classical
  refine ⟨fun h i j hij ↦ ?_, fun h ↦ ?_⟩
  · simpa [edgePart, hij] using congrFun (congrFun h i) j
  · ext i j
    by_cases hij : G.Adj i j
    · simp [edgePart, hij, h i j hij]
    · simp [edgePart, hij]

omit [Fintype V] in
private lemma continuous_edgePart (G : SimpleGraph V) : Continuous (edgePart G) := by
  classical
  refine continuous_matrix fun i j ↦ ?_
  by_cases hij : G.Adj i j
  · simpa [edgePart, hij] using
      continuous_id.matrix_elem i j
  · simpa [edgePart, hij] using (continuous_const : Continuous fun _ : Matrix V V ℝ ↦ (0 : ℝ))

omit [Fintype V] in
private lemma edgePart_add (G : SimpleGraph V) (X Y : Matrix V V ℝ) :
    edgePart G (X + Y) = edgePart G X + edgePart G Y := by
  classical
  ext i j
  by_cases hij : G.Adj i j <;> simp [edgePart, hij]

omit [Fintype V] in
private lemma edgePart_smul (G : SimpleGraph V) (a : ℝ) (X : Matrix V V ℝ) :
    edgePart G (a • X) = a • edgePart G X := by
  classical
  ext i j
  by_cases hij : G.Adj i j <;> simp [edgePart, hij]

/-- The feasible region of the primal program is compact. -/
theorem isCompact_feasible (G : SimpleGraph V) :
    IsCompact {X | Feasible G X} := by
  have hEq : {X | Feasible G X} =
      {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1} ∩ {X | edgePart G X = 0} := by
    ext X
    simp only [mem_ofPred_eq, mem_inter_iff, Feasible, edgePart_eq_zero_iff, and_assoc]
  rw [hEq]
  exact (isCompact_psd_trace 1).inter_right (isClosed_eq (continuous_edgePart G) continuous_const)

/-- Equation (1) is a maximum when the vertex set is nonempty. -/
theorem exists_theta_maximizer [Nonempty V] (G : SimpleGraph V) :
    ∃ X, Feasible G X ∧ objective X = theta G := by
  classical
  obtain ⟨X, hX, hmax⟩ := (isCompact_feasible G).exists_isMaxOn
    ⟨_, feasible_scaled_identity G⟩ continuous_objective.continuousOn
  exact ⟨X, hX, le_antisymm (objective_le_theta hX) (theta_le fun Y hY ↦ hmax hY)⟩

private lemma pairing_transpose_left (A B : Matrix V V ℝ) (hB : B.IsHermitian) :
    pairing Aᵀ B = pairing A B := by
  unfold pairing
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by
    have hij : B j i = B i j := by simpa using hB.apply i j
    rw [transpose_apply, hij]

private lemma approx_dual [Nonempty V] [DecidableEq V] (G : SimpleGraph V) {t : ℝ} (ht : theta G < t) :
    ∃ Y : Matrix V V ℝ, (∀ i j, ¬G.Adj i j → Y i j = 0) ∧
      (t • (1 : Matrix V V ℝ) - allOnes + Y).PosSemidef := by
  classical
  let A : Set (Matrix V V ℝ) := {X | X.PosSemidef ∧ X.trace = 1}
  let L : Matrix V V ℝ →ₗ[ℝ] (V → V → ℝ) × ℝ :=
    { toFun := fun X ↦ (edgePart G X, objective X)
      map_add' := fun X Y ↦ Prod.ext (edgePart_add G X Y) (objective_add X Y)
      map_smul' := fun r X ↦ Prod.ext (edgePart_smul G r X) (objective_smul r X) }
  have hEdgeContinuous : Continuous (fun X : Matrix V V ℝ ↦ (edgePart G X : V → V → ℝ)) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ (continuous_edgePart G).matrix_elem i j
  have hL : Continuous L := hEdgeContinuous.prodMk continuous_objective
  have hOutside : (0, t) ∉ L '' A := by
    rintro ⟨X, hX, hEq⟩
    have hEdge : edgePart G X = 0 := congrArg Prod.fst hEq
    have hObj : objective X = t := congrArg Prod.snd hEq
    have hFeas : Feasible G X := ⟨hX.1, hX.2, edgePart_eq_zero_iff.mp hEdge⟩
    exact (objective_le_theta hFeas).not_gt (hObj ▸ ht)
  obtain ⟨f, u, hSep, hu⟩ := geometric_hahn_banach_closed_point
    ((convex_psd_trace (V := V) 1).linear_image L)
    ((isCompact_psd_trace (V := V) 1).image hL).isClosed hOutside
  let lam : ℝ := f (0, 1)
  have hsplit (X : V → V → ℝ) (s : ℝ) : f (X, s) = f (X, 0) + s * lam := by
    have hEq : (X, s) = (X, 0) + s • (0, 1) := by simp
    rw [hEq, map_add, map_smul]
    rfl
  obtain ⟨X₀, hX₀, hopt⟩ := exists_theta_maximizer G
  have hL₀ : L X₀ = (0, theta G) :=
    Prod.ext (edgePart_eq_zero_iff.mpr hX₀.2.2) hopt
  have hlam' := (hSep (L X₀) ⟨X₀, ⟨hX₀.1, hX₀.2.1⟩, rfl⟩).trans hu
  rw [hL₀, hsplit 0 (theta G), hsplit 0 t] at hlam'
  have hlam : 0 < lam := by
    by_contra! h
    nlinarith only [hlam', mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.le) h]
  let H : Matrix V V ℝ := fun i j ↦ f (edgePart G (single i j 1), 0)
  have hH : ∀ i j, ¬G.Adj i j → H i j = 0 := by
    intro i j hij
    have hz : edgePart G (single i j 1) = 0 := edgePart_eq_zero_iff.mpr (by
      intro k l hkl
      by_cases hik : i = k
      · subst k
        have hjl : l ≠ j := fun h ↦ hij (h ▸ hkl)
        simp [Matrix.single, hjl.symm]
      · simp [Matrix.single, hik])
    rw [show H i j = f (edgePart G (single i j 1), 0) from rfl, hz]
    exact map_zero f
  let g : Matrix V V ℝ →ₗ[ℝ] ℝ :=
    f.toLinearMap.comp ((LinearMap.inl ℝ (V → V → ℝ) ℝ).comp
      ((LinearMap.fst ℝ (V → V → ℝ) ℝ).comp L))
  have hPair (X : Matrix V V ℝ) : g X = pairing H X := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, pairing]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    have hSingle : single i j (X i j) = (X i j) • single i j (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hSingle, map_smul, smul_eq_mul, mul_comm]
    rfl
  let Y : Matrix V V ℝ := (-(2 * lam)⁻¹) • (H + Hᵀ)
  have hY : Y.IsHermitian := by
    ext i j
    simp [Y, add_comm]
  have hYSupport (i j : V) (h : ¬G.Adj i j) : Y i j = 0 := by
    have hji : ¬G.Adj j i := fun h' ↦ h h'.symm
    simp [Y, hH i j h, hH j i hji]
  have hYPair (X : Matrix V V ℝ) (hX : X.IsHermitian) :
      pairing Y X = -(pairing H X / lam) := by
    rw [pairing_smul_left, pairing_add_left, pairing_transpose_left _ _ hX]
    field_simp
    ring
  have hCert (X : Matrix V V ℝ) (hX : X.PosSemidef) (hTr : X.trace = 1) :
      0 ≤ pairing (t • (1 : Matrix V V ℝ) - allOnes + Y) X := by
    have h := (hSep (L X) ⟨X, ⟨hX, hTr⟩, rfl⟩).trans hu
    change f (edgePart G X, objective X) < f (0, t) at h
    rw [hsplit (edgePart G X) (objective X), hsplit 0 t] at h
    change g X + objective X * lam < f (0, 0) + t * lam at h
    have hz : f (0, 0) = 0 := map_zero f
    rw [hz, zero_add, hPair] at h
    rw [pairing_add_left, pairing_sub_left, pairing_smul_left, pairing_one, hTr, mul_one,
      ← objective_eq_pairing, hYPair _ hX.isHermitian]
    have hDiv := (div_lt_iff₀ hlam).mpr (show pairing H X < (t - objective X) * lam by linarith)
    linarith
  refine ⟨Y, hYSupport, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
  · exact ((Matrix.isHermitian_one.smul (star_trivial t)).sub posSemidef_allOnes.isHermitian).add hY
  · intro x
    rw [star_trivial, ← pairing_vecMulVec]
    let X := vecMulVec x x
    have hX : X.PosSemidef := by simpa [X] using posSemidef_vecMulVec_self_star x
    change 0 ≤ pairing _ X
    by_cases hTr : X.trace = 0
    · rw [hX.trace_eq_zero_iff.mp hTr]
      simp [pairing]
    · have hPos : 0 < X.trace := lt_of_le_of_ne hX.trace_nonneg (Ne.symm hTr)
      have h := hCert (X.trace⁻¹ • X) (hX.smul (by positivity))
        (by simp [hTr])
      have hscale (B : Matrix V V ℝ) : pairing B (X.trace⁻¹ • X) = X.trace⁻¹ * pairing B X := by
        simp only [pairing, Matrix.smul_apply, smul_eq_mul, mul_left_comm, mul_sum]
      rw [hscale] at h
      exact nonneg_of_mul_nonneg_right h (inv_pos.mpr hPos)

/-- Strict feasibility at the scaled identity gives an attained dual certificate. -/
theorem exists_dual_certificate [Nonempty V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ Y : Matrix V V ℝ, (∀ i j, ¬G.Adj i j → Y i j = 0) ∧
      (theta G • (1 : Matrix V V ℝ) - allOnes + Y).PosSemidef := by
  classical
  let t : ℕ → ℝ := fun n ↦ theta G + ((n : ℝ) + 1)⁻¹
  have ht (n : ℕ) : theta G < t n := lt_add_of_pos_right _ (by positivity)
  choose Y hY hQ using fun n ↦ approx_dual G (ht n)
  let Q : ℕ → Matrix V V ℝ := fun n ↦ t n • (1 : Matrix V V ℝ) - allOnes + Y n
  have hQdiag (n : ℕ) (i : V) : Q n i i = t n - 1 := by
    simp [Q, allOnes, hY n i i G.irrefl]
  have hTrace (n : ℕ) : (Q n).trace ≤ Fintype.card V * theta G := by
    simp only [Matrix.trace, Matrix.diag, hQdiag, sum_const, card_univ, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := inv_le_one_of_one_le₀ (show 1 ≤ (n : ℝ) + 1 by exact le_add_of_nonneg_left (Nat.cast_nonneg n))
    dsimp [t]
    linarith
  let box : Set (Matrix V V ℝ) :=
    Set.pi univ fun _ ↦ Set.pi univ fun _ ↦
      Icc (-(Fintype.card V * theta G)) (Fintype.card V * theta G)
  have hBox : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hQbox : ∀ n, Q n ∈ box := fun n i _ j _ ↦
    abs_le.mp ((abs_apply_le_trace (hQ n) i j).trans (hTrace n))
  let : FirstCountableTopology (Matrix V V ℝ) := by
    change FirstCountableTopology (V → V → ℝ)
    infer_instance
  obtain ⟨B, _, φ, hφ, hlim⟩ := hBox.isSeqCompact hQbox
  have hBpsd : B.PosSemidef :=
    isClosed_setOfPred_posSemidef.mem_of_tendsto hlim
      (Eventually.of_forall fun n ↦ hQ (φ n))
  let Y₀ := B - theta G • (1 : Matrix V V ℝ) + allOnes
  have htlim : Tendsto t atTop (𝓝 (theta G)) := by
    have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa [t] using tendsto_const_nhds.add hzero
  refine ⟨Y₀, fun i j hij ↦ ?_, ?_⟩
  · have hEval : Continuous fun M : Matrix V V ℝ ↦ M i j :=
      continuous_id.matrix_elem i j
    have hLim₁ := (hEval.tendsto B).comp hlim
    have hLim₂ : Tendsto (fun n ↦ Q (φ n) i j) atTop
        (𝓝 (theta G * (1 : Matrix V V ℝ) i j - 1)) := by
      simpa [Q, allOnes, hY _ i j hij] using
        (((htlim.comp hφ.tendsto_atTop).mul_const ((1 : Matrix V V ℝ) i j)).sub_const 1)
    have heq := tendsto_nhds_unique hLim₁ hLim₂
    simp [Y₀, allOnes, heq]
  · simpa [Y₀, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hBpsd

/-- The product bound in the introduction, using the dual optimum of the graph. -/
theorem card_le_theta_mul_theta_compl [Nonempty V] (G : SimpleGraph V) :
    (Fintype.card V : ℝ) ≤ theta G * theta Gᶜ := by
  classical
  obtain ⟨Y, hY, hQ⟩ := exists_dual_certificate G
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have htheta : 0 < theta G := zero_lt_one.trans_le (one_le_theta G)
  let Q := theta G • (1 : Matrix V V ℝ) - allOnes + Y
  let X := (N * theta G)⁻¹ • (Q + allOnes)
  have hsum : Q + allOnes = theta G • (1 : Matrix V V ℝ) + Y := by
    simp [Q, add_comm, add_left_comm, sub_eq_add_neg]
  have hTraceY : Y.trace = 0 := by simp [Matrix.trace, hY _ _ G.irrefl]
  have hX : Feasible Gᶜ X := by
    refine ⟨(hQ.add posSemidef_allOnes).smul (by positivity), ?_, ?_⟩
    · change ((N * theta G)⁻¹ • (Q + allOnes)).trace = 1
      rw [hsum, trace_smul, trace_add, trace_smul, trace_one, hTraceY, add_zero, smul_eq_mul,
        smul_eq_mul, mul_comm (theta G) (Fintype.card V : ℝ)]
      exact inv_mul_cancel₀ (mul_ne_zero hN.ne' htheta.ne')
    · intro i j hij
      obtain ⟨hne, hadj⟩ := (SimpleGraph.compl_adj G i j).mp hij
      change ((N * theta G)⁻¹ • (Q + allOnes) : Matrix V V ℝ) i j = 0
      rw [hsum]
      simp [hY i j hadj, hne]
  have hXobj : N / theta G ≤ objective X := by
    have hQobj : 0 ≤ objective Q := objective_nonneg hQ
    rw [show objective X = (N * theta G)⁻¹ * (objective Q + N ^ 2) by
      rw [objective_smul, objective_add, objective_allOnes]]
    have hNobj : N / theta G = (N * theta G)⁻¹ * N ^ 2 := by field_simp
    rw [hNobj]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hQobj) (by positivity)
  exact (div_le_iff₀ htheta).mp (hXobj.trans (objective_le_theta hX)) |>.trans_eq (mul_comm _ _)

end LovaszTheta
