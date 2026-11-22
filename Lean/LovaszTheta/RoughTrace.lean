module

public import LovaszTheta.RoughPath

/-!
# The colored trace moment

Expanding the trace gives a cyclic sequence of vertex labelings. Sign
orthogonality counts the color-compatible sequences with even
multiplicity at every labeled edge.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix

namespace LovaszTheta.Independent

variable {V : Type*} [Fintype V]

private abbrev pathVertices (a : V) {k : ℕ} (x : Fin k → V) (b : V) : Fin (k+2) → V :=
  Fin.cons (α := fun _ ↦ V) a (Fin.snoc (α := fun _ ↦ V) x b)

private lemma pow_succ_apply_eq_sum_path (A : Matrix V V ℝ) (k : ℕ) (a b : V) :
    (A ^ (k + 1)) a b = ∑ x : Fin k → V, ∏ i : Fin (k + 1),
      A (pathVertices a x b i.castSucc) (pathVertices a x b i.succ) := by
  induction k generalizing a with
  | zero =>
    have hLast (x : Fin 0 → V) : Fin.snoc (α := fun _ ↦ V) x b (0 : Fin 1) = b :=
      @Fin.snoc_last 0 (fun _ ↦ V) b x
    simp [pathVertices, hLast]
  | succ k ih =>
    calc
      _ = ∑ p : V × (Fin k → V), A a p.1 * ∏ i : Fin (k + 1),
          A (pathVertices p.1 p.2 b i.castSucc) (pathVertices p.1 p.2 b i.succ) := by
        rw [pow_succ' A (k+1), Matrix.mul_apply]
        simp only [ih, Fintype.sum_prod_type, mul_sum]
      _ = _ := by
        refine Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ V)) _ _ ?_
        rintro ⟨c, x⟩
        simp only [Fin.consEquiv_apply, pathVertices,
          ← Fin.cons_snoc_eq_snoc_cons]
        conv_rhs => rw [Fin.prod_univ_succ]
        have hShift (i : Fin (k+1)) : i.succ.castSucc = i.castSucc.succ := rfl
        simp only [hShift, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]

/-- Trace powers expand over cyclic sequences of row indices. -/
lemma trace_pow_succ_eq_sum_cycle (A : Matrix V V ℝ) (k : ℕ) :
    (A ^ (k + 1)).trace =
      ∑ a : Fin (k+1) → V, ∏ i : Fin (k+1), A (a i) (a (finRotate (k+1) i)) := by
  calc
    _ = ∑ p : V × (Fin k → V), ∏ i : Fin (k+1),
          A (pathVertices p.1 p.2 p.1 i.castSucc) (pathVertices p.1 p.2 p.1 i.succ) := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, pow_succ_apply_eq_sum_path]
    _ = _ := by
      refine Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ V)) _ _ ?_
      rintro ⟨a, x⟩
      simp only [Fin.consEquiv_apply, pathVertices, Fin.cons_snoc_eq_snoc_cons]
      apply prod_congr rfl
      intro i _
      let rows := Fin.cons (α := fun _ ↦ V) a x
      change A (Fin.snoc (α := fun _ ↦ V) rows a i.castSucc)
        (Fin.snoc (α := fun _ ↦ V) rows a i.succ) = A (rows i) (rows (finRotate (k+1) i))
      rw [Fin.snoc_castSucc]
      exact congrArg (A (rows i)) (snoc_first_succ rows i)

private lemma trace_mul_transpose_pow_eq_sum (A : Matrix V V ℝ) (k : ℕ) :
    ((A * Aᵀ) ^ (k + 1)).trace =
      ∑ a : Fin (k + 1) → V, ∑ b : Fin (k + 1) → V, ∏ i : Fin (k + 1) × Bool,
        A (if i.2 then a (finRotate (k + 1) i.1) else a i.1) (b i.1) := by
  rw [trace_pow_succ_eq_sum_cycle]
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp [Fintype.prod_prod_type, mul_comm]

variable (α : Shape) {k : ℕ}
variable (color : V → Fin α.vertexCount)

private def traceCompatible (f : Fin k × Bool → (Fin α.vertexCount ↪ V)) : Prop :=
  (∀ i a, color (f i a) = a) ∧
  (∀ i, f (i, false) α.right = f (i, true) α.right) ∧
  ∀ i, f (i, true) α.left = f (finRotate k i, false) α.left

private def traceEven (f : Fin k × Bool → (Fin α.vertexCount ↪ V)) : Prop :=
  ∀ e : EdgeIndex V, Even ((univ.filter fun i ↦ e ∈ labelledEdges α (f i)).card)

private def traceRows (f : Fin k × Bool → (Fin α.vertexCount ↪ V)) (i : Fin k) : V :=
  f (i, false) α.left

private def traceColumns (f : Fin k × Bool → (Fin α.vertexCount ↪ V)) (i : Fin k) : V :=
  f (i, false) α.right

omit [Fintype V] in
private lemma trace_entry_conditions_iff (f : Fin k × Bool → (Fin α.vertexCount ↪ V))
    (a b : Fin k → V) :
    (∀ i : Fin k × Bool,
        (f i α.left = (if i.2 then a (finRotate k i.1) else a i.1) ∧ f i α.right = b i.1) ∧
        (∀ v, color (f i v) = v)) ↔
      traceCompatible α color f ∧ a = traceRows α f ∧ b = traceColumns α f := by
  constructor
  · intro h
    have hLeft (i : Fin k) : f (i, false) α.left = a i := (h (i, false)).1.1
    have hRight (i : Fin k) : f (i, false) α.right = b i := (h (i, false)).1.2
    refine ⟨⟨fun i ↦ (h i).2, ?_, ?_⟩, funext fun i ↦ (hLeft i).symm,
      funext fun i ↦ (hRight i).symm⟩
    · intro i
      exact (hRight i).trans (h (i, true)).1.2.symm
    · intro i
      exact (h (i, true)).1.1.trans (hLeft (finRotate k i)).symm
  · rintro ⟨⟨hColor, hRight, hLeft⟩, rfl, rfl⟩ ⟨i, orientation⟩
    cases orientation
    · exact ⟨⟨rfl, rfl⟩, hColor _⟩
    · exact ⟨⟨hLeft i, (hRight i).symm⟩, hColor _⟩

private lemma trace_colored_pow_eq_sum (x : EdgeIndex V → Bool) (k : ℕ) :
    let A := coloredGraphMatrix α x color
    ((A * Aᵀ) ^ (k + 1)).trace =
      ∑ f : Fin (k+1) × Bool → (Fin α.vertexCount ↪ V),
        if traceCompatible α color f then ∏ i, walsh (labelledEdges α (f i)) x else 0 := by
  let A := coloredGraphMatrix α x color
  change ((A * Aᵀ) ^ (k + 1)).trace = _
  rw [trace_mul_transpose_pow_eq_sum]
  simp only [A, coloredGraphMatrix, Fintype.prod_sum]
  have hProd (a b : Fin (k+1) → V) (f : Fin (k+1) × Bool → (Fin α.vertexCount ↪ V)) :
      (∏ i : Fin (k+1) × Bool,
        if (f i α.left = (if i.2 then a (finRotate (k+1) i.1) else a i.1) ∧
            f i α.right = b i.1) ∧ (∀ v, color (f i v) = v)
        then walsh (labelledEdges α (f i)) x else 0) =
      if traceCompatible α color f ∧ a = traceRows α f ∧ b = traceColumns α f
      then ∏ i, walsh (labelledEdges α (f i)) x else 0 := by
    simp only [← trace_entry_conditions_iff α color f a b]
    split_ifs with h
    · exact prod_congr rfl fun i _ ↦ ite_eq_left (h i)
    · simp only [not_forall] at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [hProd]
  let term (a b : Fin (k+1) → V) (f : Fin (k+1) × Bool → (Fin α.vertexCount ↪ V)) : ℝ :=
    if traceCompatible α color f ∧ a = traceRows α f ∧ b = traceColumns α f
    then ∏ i, walsh (labelledEdges α (f i)) x else 0
  change (∑ a, ∑ b, ∑ f, term a b f) = _
  calc
    _ = ∑ a, ∑ f, ∑ b, term a b f := sum_congr rfl fun a _ ↦ sum_comm
    _ = ∑ f, ∑ a, ∑ b, term a b f := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro f _
      by_cases h : traceCompatible α color f
      · simp [term, h, ite_and]
      · simp [term, h]

private lemma average_sign_pow (m : ℕ) :
    average (fun b ↦ sign b ^ m) = if Even m then 1 else 0 := by
  simp only [average, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat, sign_true, one_pow,
    sign_false, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

/-- A product of sign characters has mean one exactly when every
sign occurs with even multiplicity. -/
lemma average_walsh_prod {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (S : J → Finset ι) :
    average (fun x ↦ ∏ j, walsh (S j) x) =
      if ∀ b : ι, Even ((univ.filter fun j ↦ b ∈ S j).card) then 1 else 0 := by
  have hProd (x : ι → Bool) (j : J) :
      walsh (S j) x = ∏ b, if b ∈ S j then sign (x b) else 1 := by
    rw [prod_ite_mem, univ_inter, walsh]
  simp_rw [hProd]
  rw [show (fun x : ι → Bool ↦ ∏ j, ∏ b, if b ∈ S j then sign (x b) else 1) =
      (fun x ↦ ∏ b, ∏ j, if b ∈ S j then sign (x b) else 1) from
    funext fun _ ↦ prod_comm]
  have hFactor (x : ι → Bool) (b : ι) :
      (∏ j, if b ∈ S j then sign (x b) else 1) =
        sign (x b) ^ ((univ.filter fun j ↦ b ∈ S j).card) := by simp [Finset.prod_ite]
  simp_rw [hFactor]
  rw [average_product (fun b c ↦ sign c ^ ((univ.filter fun j ↦ b ∈ S j).card))]
  simp_rw [average_sign_pow]
  split_ifs with h
  · exact prod_eq_one fun b _ ↦ ite_eq_left (h b)
  · simp only [not_forall] at h
    obtain ⟨b, hb⟩ := h
    exact prod_eq_zero (mem_univ b) (ite_eq_right hb)

private def coloredTrace_equiv (k : ℕ) :
    ColoredTrace α k color ≃
      {f : Fin k × Bool → (Fin α.vertexCount ↪ V) // traceCompatible α color f ∧ traceEven α f} where
  toFun t := ⟨t.labelling, ⟨t.color_eq, t.right_eq, t.left_eq⟩, t.even_edges⟩
  invFun t := ⟨t.val, t.property.1.1, t.property.1.2.1, t.property.1.2.2, t.property.2⟩
  left_inv := fun ⟨_, _, _, _, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

noncomputable instance (k : ℕ) : Fintype (ColoredTrace α k color) :=
  Fintype.ofInjective ColoredTrace.labelling (by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl)

/-- The expectation of the colored trace moment is the number of compatible
labelings with even multiplicity at every sign. -/
theorem average_trace_coloredGraphMatrix_pow (k : ℕ) :
    average (fun x : EdgeIndex V → Bool ↦
      let A := coloredGraphMatrix α x color
      ((A * Aᵀ) ^ (k + 1)).trace) = (Fintype.card (ColoredTrace α (k+1) color) : ℝ) := by
  simp_rw [trace_colored_pow_eq_sum, average_sum]
  have hAvg (f : Fin (k+1) × Bool → (Fin α.vertexCount ↪ V)) :
      average (fun x : EdgeIndex V → Bool ↦
        if traceCompatible α color f then ∏ i, walsh (labelledEdges α (f i)) x else 0) =
      if traceCompatible α color f ∧ traceEven α f then 1 else 0 := by
    by_cases hc : traceCompatible α color f
    · simp only [hc, ite_true, true_and]
      rw [average_walsh_prod (fun i ↦ labelledEdges α (f i))]
      by_cases he : traceEven α f
      · rw [ite_eq_left he]
        unfold traceEven at he
        exact ite_eq_left he
      · rw [ite_eq_right he]
        unfold traceEven at he
        exact ite_eq_right he
    · simp [hc]
  simp_rw [hAvg]
  rw [Fintype.card_congr (coloredTrace_equiv α color (k+1)), Fintype.card_subtype, card_filter]
  push_cast
  exact sum_congr rfl fun f _ ↦ by split_ifs <;> norm_num

end LovaszTheta.Independent
