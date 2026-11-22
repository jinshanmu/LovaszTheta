module

public import LovaszTheta.RoughTrace

/-!
# Equality patterns of trace labels

An equality pattern chooses a representative position for each label.
The pattern and the labels of those representatives determine the
entire array.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

private noncomputable def representative {I V : Type*} (f : I → V) (v : Set.range f) : I :=
  v.property.choose

private noncomputable def pattern {I V : Type*} (f : I → V) (i : I) : I :=
  representative f ⟨f i, ⟨i, rfl⟩⟩

private lemma apply_pattern {I V : Type*} (f : I → V) (i : I) :
    f (pattern f i) = f i :=
  (show f i ∈ Set.range f from ⟨i, rfl⟩).choose_spec

private lemma pattern_congr {I V : Type*} {f : I → V} {i j : I} (h : f i = f j) :
    pattern f i = pattern f j :=
  congrArg (representative f) (Subtype.ext h)

private lemma card_pattern_le {I V : Type*} [Fintype I] (f : I → V) :
    (univ.image (pattern f)).card ≤ (univ.image f).card := by
  apply card_le_card_of_injOn f
  · intro i hi
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  · intro i hi j hj he
    obtain ⟨r, _, hr⟩ := mem_image.mp hi
    obtain ⟨s, _, hs⟩ := mem_image.mp hj
    rw [← hr, ← hs] at he ⊢
    rw [apply_pattern f r, apply_pattern f s] at he
    exact pattern_congr he

/-- At most `card I ^ card I` equality patterns occur on a set of positions
`I`. Within a pattern with at most `L` labels, at most `card V ^ L`
assignments give the concrete labels. -/
theorem card_le_of_bounded_labels {Ω I V : Type*} [Fintype Ω] [Fintype I] [Fintype V]
    [Nonempty V] (f : Ω → I → V) (hf : Function.Injective f) (L : ℕ)
    (hL : ∀ x, (univ.image (f x)).card ≤ L) :
    Fintype.card Ω ≤ (Fintype.card I) ^ Fintype.card I * (Fintype.card V) ^ L := by
  let K := {p : I → I // (univ.image p).card ≤ L}
  let data := Σ p : K, (↥(univ.image p.val) → V)
  let code (x : Ω) : data :=
    ⟨⟨pattern (f x), (card_pattern_le (f x)).trans (hL x)⟩, fun i ↦ f x i⟩
  let decode (d : data) (i : I) : V :=
    d.2 ⟨d.1.val i, mem_image_of_mem _ (mem_univ _)⟩
  have hDecode (x : Ω) (i : I) : decode (code x) i = f x i := apply_pattern _ _
  have hInj : Function.Injective code := by
    intro x y he
    apply hf
    funext i
    rw [← hDecode x i, ← hDecode y i, he]
  have hK : Fintype.card K ≤ (Fintype.card I) ^ Fintype.card I := by
    rw [← Fintype.card_fun]
    exact Fintype.card_le_of_injective _ Subtype.val_injective
  calc
    Fintype.card Ω ≤ Fintype.card data := Fintype.card_le_of_injective code hInj
    _ = ∑ p : K, (Fintype.card V) ^ (univ.image p.val).card := by
      simp only [data, Fintype.card_sigma, Fintype.card_fun, Fintype.card_coe]
    _ ≤ ∑ _p : K, (Fintype.card V) ^ L := by
      exact sum_le_sum fun p _ ↦ Nat.pow_le_pow_right Fintype.card_pos p.property
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ hK

variable {V : Type*} [Fintype V] [Nonempty V]

/-- The boundary connectivity correction in the rough moment exponent. -/
noncomputable def Shape.boundaryIndicator (α : Shape) : ℕ :=
  if α.graph.Reachable α.left α.right then 1 else 0

/-- Bound on the number of distinct labels in a contributing trace term. -/
noncomputable def Shape.traceLabelBound (α : Shape) (k : ℕ) : ℕ :=
  k * (α.vertexCount + α.isolatedInterior.card - α.boundaryIndicator) + α.boundaryIndicator

omit [Fintype V] [Nonempty V] in
private lemma ColoredTrace.card_labels_le_bound {α : Shape} {k : ℕ}
    {color : V → Fin α.vertexCount} (t : ColoredTrace α k color) (hk : 0 < k) :
    t.labels.card ≤ α.traceLabelBound k := by
  by_cases h : α.graph.Reachable α.left α.right
  · simpa only [Shape.traceLabelBound, Shape.boundaryIndicator, h, ite_true] using
      t.card_labels_le_of_connected hk h
  · simpa only [Shape.traceLabelBound, Shape.boundaryIndicator, h, ite_false, Nat.sub_zero,
      Nat.add_zero] using t.card_labels_le

/-- All contributing colored trace terms are bounded by the number of
equality patterns times the number of assignments for each pattern. -/
theorem card_coloredTrace_le (α : Shape) {k : ℕ} (hk : 0 < k)
    (color : V → Fin α.vertexCount) :
    Fintype.card (ColoredTrace α k color) ≤
      (2 * k * α.vertexCount) ^ (2 * k * α.vertexCount) *
        (Fintype.card V) ^ α.traceLabelBound k := by
  let f (t : ColoredTrace α k color) (j : (Fin k × Bool) × Fin α.vertexCount) : V :=
    t.labelling j.1 j.2
  have hInj : Function.Injective f := by
    intro t u he
    have ht : t.labelling = u.labelling := by
      funext i
      ext a
      exact congrFun he (i, a)
    cases t
    cases u
    cases ht
    rfl
  have hL (t : ColoredTrace α k color) : (univ.image (f t)).card ≤ α.traceLabelBound k := by
    convert t.card_labels_le_bound hk using 1
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_biUnion.mpr ⟨a, mem_univ _, mem_image_of_mem _ (mem_univ i)⟩
    · intro hx
      obtain ⟨a, _, ha⟩ := mem_biUnion.mp hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp ha
      exact mem_image_of_mem _ (mem_univ (i, a))
  have hc : Fintype.card ((Fin k × Bool) × Fin α.vertexCount) = 2*k*α.vertexCount := by
    simp [Fintype.card_prod, mul_comm]
  simpa only [hc] using card_le_of_bounded_labels f hInj _ hL

end LovaszTheta.Independent
