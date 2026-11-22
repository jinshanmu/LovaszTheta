module

public import LovaszTheta.RandomGraphs
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Graph matrices for independent edges

A shape is a graph with two designated boundary vertices. The matrix entries
sum over injective labelings, so the sign support of a summand consists of
distinct unordered pairs. These definitions also give the color-restricted
matrices and the exact cancellation in a product of two graph matrices.
-/

@[expose] public section

open Finset Matrix
open scoped Classical Matrix symmDiff

namespace LovaszTheta.Independent

/-- A graph shape with possibly coincident ordered boundaries. -/
structure Shape where
  /-- The number of vertices of the shape. -/
  vertexCount : ℕ
  /-- The underlying simple graph. -/
  graph : SimpleGraph (Fin vertexCount)
  /-- The left boundary vertex. -/
  left : Fin vertexCount
  /-- The right boundary vertex. -/
  right : Fin vertexCount

noncomputable instance (α : Shape) : Fintype (α.graph.edgeSet) :=
  Fintype.ofFinite _

/-- Reversal of the ordered boundaries. -/
def Shape.reverse (α : Shape) : Shape :=
  { α with left := α.right, right := α.left }

/-- Label an unordered edge of the shape using a vertex embedding. -/
def edgeEmbedding {V : Type*} (α : Shape) (f : Fin α.vertexCount ↪ V) :
    α.graph.edgeSet ↪ EdgeIndex V where
  toFun e := ⟨e.val.map f, fun h ↦ α.graph.not_isDiag_of_mem_edgeSet e.property
    ((Sym2.isDiag_map f.injective).mp h)⟩
  inj' := fun _ _ h ↦ Subtype.ext (Sym2.map.injective f.injective (congrArg Subtype.val h))

/-- The sign indices used by an injective labeling of the shape. -/
noncomputable def labelledEdges {V : Type*} (α : Shape) (f : Fin α.vertexCount ↪ V) :
    Finset (EdgeIndex V) :=
  univ.map (edgeEmbedding α f)

lemma walsh_labelledEdges {V : Type*} (α : Shape) (f : Fin α.vertexCount ↪ V)
    (x : EdgeIndex V → Bool) :
    walsh (labelledEdges α f) x = ∏ e : α.graph.edgeSet, sign (x (edgeEmbedding α f e)) := by
  rw [walsh, labelledEdges, Finset.prod_map]

/-- The graph matrix of a shape, expanded in the independent sign variables. -/
noncomputable def graphMatrix {V : Type*} [Fintype V] (α : Shape) (x : EdgeIndex V → Bool) :
    Matrix V V ℝ := by
  classical
  exact fun i j ↦ ∑ f : Fin α.vertexCount ↪ V,
    if f α.left = i ∧ f α.right = j then walsh (labelledEdges α f) x else 0

lemma graphMatrix_reverse {V : Type*} [Fintype V] (α : Shape) (x : EdgeIndex V → Bool) :
    graphMatrix α.reverse x = (graphMatrix α x)ᵀ := by
  classical
  ext i j
  simp only [graphMatrix, transpose_apply]
  exact sum_congr rfl fun f _ ↦ by
    change (if f α.right = i ∧ f α.left = j then walsh (labelledEdges α f) x else 0) =
      if f α.left = j ∧ f α.right = i then walsh (labelledEdges α f) x else 0
    by_cases h : f α.left = j ∧ f α.right = i
    · simp only [ite_eq_left h, ite_eq_left h.symm]
    · have h' : ¬(f α.right = i ∧ f α.left = j) := fun hh ↦ h hh.symm
      simp only [ite_eq_right h, ite_eq_right h']

/-- The matrix with each shape vertex restricted to its color class. -/
noncomputable def coloredGraphMatrix {V : Type*} [Fintype V] (α : Shape)
    (x : EdgeIndex V → Bool) (color : V → Fin α.vertexCount) : Matrix V V ℝ := by
  classical
  exact fun i j ↦ ∑ f : Fin α.vertexCount ↪ V,
    if (f α.left = i ∧ f α.right = j) ∧ (∀ a, color (f a) = a)
    then walsh (labelledEdges α f) x else 0

private lemma average_color_indicator {V : Type*} [Fintype V]
    (α : Shape) (f : Fin α.vertexCount ↪ V) :
    average (fun (color : V → Fin α.vertexCount) ↦
      if ∀ a, color (f a) = a then (1 : ℝ) else 0) = (α.vertexCount : ℝ)⁻¹ ^ α.vertexCount := by
  classical
  let range := (univ : Finset (Fin α.vertexCount)).map f
  have exists_preimage (i : V) (hi : i ∈ range) : ∃ a, f a = i := by
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hi
    exact ⟨a, ha⟩
  let test (i : V) (c : Fin α.vertexCount) : ℝ :=
    if hi : i ∈ range then if c = (exists_preimage i hi).choose then 1 else 0 else 1
  have hTest (color : V → Fin α.vertexCount) :
      (if ∀ a, color (f a) = a then (1 : ℝ) else 0) = ∏ i, test i (color i) := by
    by_cases hc : ∀ a, color (f a) = a
    · rw [ite_eq_left hc]
      symm
      apply prod_eq_one
      intro i _
      by_cases hi : i ∈ range
      · have hEq : color i = (exists_preimage i hi).choose :=
          (congrArg color (exists_preimage i hi).choose_spec.symm).trans
            (hc (exists_preimage i hi).choose)
        simp only [test, dite_eq_left hi, ite_eq_left hEq]
      · simp [test, hi]
    · rw [ite_eq_right hc]
      push Not at hc
      obtain ⟨a, ha⟩ := hc
      have hi : f a ∈ range := Finset.mem_map.mpr ⟨a, mem_univ a, rfl⟩
      have hEq : (exists_preimage (f a) hi).choose = a :=
        f.injective (exists_preimage (f a) hi).choose_spec
      symm
      apply Finset.prod_eq_zero (mem_univ (f a))
      have hNe : color (f a) ≠ (exists_preimage (f a) hi).choose := by
        rwa [hEq]
      simp only [test, dite_eq_left hi, ite_eq_right hNe]
  let : Nonempty (Fin α.vertexCount) := ⟨α.left⟩
  have hMean (i : V) :
      average (test i) = if i ∈ range then (α.vertexCount : ℝ)⁻¹ else 1 := by
    by_cases hi : i ∈ range
    · simp [test, hi, average, one_div]
    · simpa only [test, dite_eq_right hi, ite_eq_right hi] using
        average_const (Ω := Fin α.vertexCount) (1 : ℝ)
  simp_rw [hTest]
  rw [average_product test]
  simp only [hMean, prod_ite, filter_mem_eq_inter, univ_inter]
  simp [range]

/-- Averaging the color restriction retains each injective labeling with probability
`vertexCount ^ (-vertexCount)`. This is the coloring identity in Lemma 2.1. -/
theorem average_coloredGraphMatrix {V : Type*} [Fintype V] (α : Shape)
    (x : EdgeIndex V → Bool) (i j : V) :
    average (fun color ↦ coloredGraphMatrix α x color i j) =
      (α.vertexCount : ℝ)⁻¹ ^ α.vertexCount * graphMatrix α x i j := by
  classical
  simp only [coloredGraphMatrix, graphMatrix, average_sum, mul_sum]
  apply sum_congr rfl
  intro f _
  by_cases hf : f α.left = i ∧ f α.right = j
  · simp only [hf, true_and, ite_true]
    have h := average_color_indicator α f
    have hFact (color : V → Fin α.vertexCount) :
        (if ∀ a, color (f a) = a then walsh (labelledEdges α f) x else 0) =
        walsh (labelledEdges α f) x * (if ∀ a, color (f a) = a then 1 else 0) := by
      split_ifs <;> simp
    simp_rw [hFact, average_mul_left, h, mul_comm (walsh _ _)]
  · simp [hf, average]

/-- The product of two graph matrices is the sum over their labelings with a common
joining label. Every edge common to the two labeled factors cancels. -/
theorem graphMatrix_mul_apply {V : Type*} [Fintype V] (α β : Shape) (x : EdgeIndex V → Bool)
    (i k : V) :
    (graphMatrix α x * graphMatrix β x) i k =
      ∑ j, ∑ f : Fin α.vertexCount ↪ V, ∑ g : Fin β.vertexCount ↪ V,
        if (f α.left = i ∧ f α.right = j) ∧ (g β.left = j ∧ g β.right = k)
        then walsh (labelledEdges α f ∆ labelledEdges β g) x else 0 := by
  classical
  simp only [Matrix.mul_apply, graphMatrix, sum_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  refine sum_congr rfl fun f _ ↦ sum_congr rfl fun g _ ↦ ?_
  by_cases hf : f α.left = i ∧ f α.right = j <;>
    by_cases hg : g β.left = j ∧ g β.right = k <;> simp [hf, hg, walsh_mul]

/-- The graph-matrix normalization for a chain, with the number of vertices including
the shared boundaries. -/
noncomputable def chainNormalization (n vertices : ℕ) : ℝ :=
  (n : ℝ) ^ (-((vertices : ℝ) - 1) / 2)

/-- The graph-matrix normalization for two separated chains. -/
noncomputable def twoChainNormalization (n vertices : ℕ) : ℝ :=
  (n : ℝ) ^ (-(vertices : ℝ) / 2)

end LovaszTheta.Independent
