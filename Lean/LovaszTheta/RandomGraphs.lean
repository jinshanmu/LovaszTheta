module

public import LovaszTheta.Duality
public import LovaszTheta.Signs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic

/-!
# The random graphs and their common lower bound

Independent edges are indexed by unordered pairs of distinct vertices.
Circulant edges are indexed by nonzero inversion classes of the cyclic group.
Negating every sign implements graph complementation in both sample spaces.
-/

@[expose] public section

open Finset

namespace LovaszTheta

/-- Simultaneous reversal of all coordinates of the sign cube. -/
def reverseSigns (ι : Type*) : (ι → Bool) ≃ (ι → Bool) :=
  (show Function.Involutive (fun (x : ι → Bool) i ↦ !(x i)) by
    intro x
    funext i
    simp).toPerm

@[simp]
lemma reverseSigns_apply {ι : Type*} (x : ι → Bool) (i : ι) :
    reverseSigns ι x i = !(x i) := rfl

/-- The common lower bound for a finite graph law invariant under complementation. -/
theorem sqrt_card_le_average_theta {Ω V : Type*} [Fintype Ω] [Nonempty Ω] [Fintype V]
    [Nonempty V] (G : Ω → SimpleGraph V) (e : Ω ≃ Ω) (he : ∀ x, G (e x) = (G x)ᶜ) :
    Real.sqrt (Fintype.card V) ≤ average (fun x ↦ theta (G x)) := by
  classical
  have hpoint (x : Ω) :
      2 * Real.sqrt (Fintype.card V) ≤ theta (G x) + theta ((G x)ᶜ) := by
    have hx := card_le_theta_mul_theta_compl (G x)
    have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card V : ℝ) by positivity)
    have hsum : 0 ≤ theta (G x) + theta ((G x)ᶜ) :=
      add_nonneg (zero_le_one.trans (one_le_theta _)) (zero_le_one.trans (one_le_theta _))
    by_contra! h
    have hd := mul_pos (sub_pos.mpr h)
      (show 0 < 2 * Real.sqrt (Fintype.card V) + (theta (G x) + theta ((G x)ᶜ)) by linarith)
    nlinarith [sq_nonneg (theta (G x) - theta ((G x)ᶜ))]
  have hMean := average_mono hpoint
  rw [average_const, average_add] at hMean
  have hComp :
      average (fun x ↦ theta ((G x)ᶜ)) = average (fun x ↦ theta (G x)) := by
    simpa only [he] using average_equiv e (fun x ↦ theta (G x))
  linarith

namespace Independent

/-- The unordered off-diagonal pairs, one independent sign per edge candidate. -/
abbrev EdgeIndex (V : Type*) := {e : Sym2 V // ¬e.IsDiag}

noncomputable instance {V : Type*} [Fintype V] : Fintype (EdgeIndex V) :=
  Fintype.ofFinite _

/-- The edge index of two distinct vertices. -/
def edgeIndex {V : Type*} (i j : V) (h : i ≠ j) : EdgeIndex V :=
  ⟨s(i, j), by simpa using h⟩

lemma edgeIndex_swap {V : Type*} (i j : V) (h : i ≠ j) :
    edgeIndex j i h.symm = edgeIndex i j h := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- The independent-edge graph, with true selecting the edge. -/
def graph {V : Type*} (x : EdgeIndex V → Bool) : SimpleGraph V where
  Adj i j := ∃ h : i ≠ j, x (edgeIndex i j h) = true
  symm := ⟨fun i j ⟨h, hx⟩ ↦ ⟨h.symm, by rwa [edgeIndex_swap]⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ ↦ h rfl⟩

lemma graph_reverseSigns {V : Type*} (x : EdgeIndex V → Bool) :
    graph (reverseSigns (EdgeIndex V) x) = (graph x)ᶜ := by
  ext i j
  rw [SimpleGraph.compl_adj]
  by_cases h : i = j
  · subst j
    simp [graph]
  · change (∃ h' : i ≠ j, !(x (edgeIndex i j h')) = true) ↔
      i ≠ j ∧ ¬∃ h' : i ≠ j, x (edgeIndex i j h') = true
    cases hx : x (edgeIndex i j h) <;> simp [h, show ∀ h', x (edgeIndex i j h') = _ from fun _ ↦ hx]

/-- The signed adjacency matrix of the independent-edge model. -/
noncomputable def signedAdjacency {V : Type*} (x : EdgeIndex V → Bool) : Matrix V V ℝ := by
  classical
  exact fun i j ↦ if h : i ≠ j then sign (x (edgeIndex i j h)) else 0

@[simp]
lemma signedAdjacency_diag {V : Type*} (x : EdgeIndex V → Bool) (i : V) :
    signedAdjacency x i i = 0 := by simp [signedAdjacency]

lemma signedAdjacency_swap {V : Type*} (x : EdgeIndex V → Bool) (i j : V) :
    signedAdjacency x j i = signedAdjacency x i j := by
  by_cases h : i = j
  · simp [h]
  · rw [signedAdjacency, signedAdjacency, dite_eq_left (Ne.symm h), dite_eq_left h,
      edgeIndex_swap i j h]

lemma signedAdjacency_edge {V : Type*} (x : EdgeIndex V → Bool) {i j : V}
    (h : (graph x).Adj i j) : signedAdjacency x i j = 1 := by
  obtain ⟨hne, hx⟩ := h
  simp [signedAdjacency, hne, hx]

lemma signedAdjacency_nonedge {V : Type*} (x : EdgeIndex V → Bool) {i j : V}
    (hne : i ≠ j) (h : ¬(graph x).Adj i j) : signedAdjacency x i j = -1 := by
  have hx : x (edgeIndex i j hne) = false :=
    Bool.eq_false_iff.mpr fun hs ↦ h ⟨hne, hs⟩
  simp [signedAdjacency, hne, hx]

/-- The expectation of theta in the independent-edge model on `n` vertices. -/
noncomputable def expectedTheta (n : ℕ) : ℝ := by
  classical
  exact average fun x ↦ theta (graph (V := Fin n) x)

theorem sqrt_le_expectedTheta (n : ℕ) [NeZero n] : Real.sqrt n ≤ expectedTheta n := by
  classical
  simpa [expectedTheta] using sqrt_card_le_average_theta (graph (V := Fin n))
    (reverseSigns (EdgeIndex (Fin n))) graph_reverseSigns

end Independent

namespace Circulant

variable {n : ℕ}

/-- An inversion class, represented by its one- or two-element set of residues. -/
def InversionClass (n : ℕ) := {s : Finset (ZMod n) // ∃ x : ZMod n, x ≠ 0 ∧ s = {x, -x}}

noncomputable instance [NeZero n] : Fintype (InversionClass n) := by
  classical
  unfold InversionClass
  infer_instance

/-- The nonzero inversion class of a residue. -/
def inversionClass (a : ZMod n) (ha : a ≠ 0) : InversionClass n :=
  ⟨{a, -a}, a, ha, rfl⟩

lemma inversionClass_neg (a : ZMod n) (ha : a ≠ 0) :
    inversionClass (-a) (by simpa using ha) = inversionClass a ha := by
  apply Subtype.ext
  simp [inversionClass, Finset.pair_comm]

lemma inversionClass_eq_iff {a b : ZMod n} (ha : a ≠ 0) (hb : b ≠ 0) :
    inversionClass a ha = inversionClass b hb ↔ a = b ∨ a = -b := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' := congrArg Subtype.val h
    change ({a, -a} : Finset (ZMod n)) = {b, -b} at h'
    have hmem : a ∈ ({b, -b} : Finset (ZMod n)) := by rw [← h']; simp
    simpa using hmem
  · rintro (h | h)
    · subst b
      rfl
    · subst a
      exact inversionClass_neg b hb

/-- Every inversion class contains at most two residues. -/
lemma inversionClass_card_le (c : InversionClass n) : c.val.card ≤ 2 := by
  obtain ⟨a, _, he⟩ := c.property
  rw [he]
  exact Finset.card_le_two

/-- The signed connection set, with the zero residue omitted. -/
noncomputable def epsilon (x : InversionClass n → Bool) (a : ZMod n) : ℝ :=
  if h : a = 0 then 0 else sign (x (inversionClass a h))

@[simp]
lemma epsilon_zero (x : InversionClass n → Bool) : epsilon x 0 = 0 := by simp [epsilon]

lemma epsilon_even (x : InversionClass n → Bool) : (epsilon x).Even := by
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · have hn : -a ≠ 0 := by simpa using ha
    rw [show epsilon x (-a) = sign (x (inversionClass (-a) hn)) by simp [epsilon, hn],
      inversionClass_neg a ha]
    simp [epsilon, ha]

/-- The random circulant graph, with false selecting the connection class. -/
def graph (x : InversionClass n → Bool) : SimpleGraph (ZMod n) where
  Adj i j := epsilon x (i - j) = -1
  symm := ⟨fun i j h ↦ by
    rw [← neg_sub i j, epsilon_even]
    exact h⟩
  loopless := ⟨fun i h ↦ by
    change epsilon x (i - i) = -1 at h
    norm_num at h⟩

lemma graph_adj_iff_epsilon (x : InversionClass n → Bool) (i j : ZMod n) :
    (graph x).Adj i j ↔ epsilon x (i - j) = -1 := Iff.rfl

lemma graph_reverseSigns (x : InversionClass n → Bool) :
    graph (reverseSigns (InversionClass n) x) = (graph x)ᶜ := by
  ext i j
  rw [SimpleGraph.compl_adj, graph_adj_iff_epsilon, graph_adj_iff_epsilon]
  by_cases h : i = j
  · subst j
    norm_num
  · have hSub : i - j ≠ 0 := sub_ne_zero.mpr h
    cases hx : x (inversionClass (i - j) hSub) <;> norm_num [epsilon, hSub, hx, h]

/-- The expectation of theta in the circulant model at positive order `n`. -/
noncomputable def expectedTheta (n : ℕ) [NeZero n] : ℝ := by
  classical
  exact average fun x ↦ theta (graph (n := n) x)

theorem sqrt_le_expectedTheta (n : ℕ) [NeZero n] : Real.sqrt n ≤ expectedTheta n := by
  classical
  simpa [expectedTheta, ZMod.card] using sqrt_card_le_average_theta (graph (n := n))
    (reverseSigns (InversionClass n)) graph_reverseSigns

end Circulant

end LovaszTheta
