module

public import LovaszTheta.BasicShapeReversal
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Chains in spanning-path order

A chain is stored with its last block first. The vertices are in
spanning-path order. Appending a block adds a final interval that
meets the old chain at its right endpoint.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

/-- Adjacency in a graph on an interval, expressed using natural positions. -/
def adjAt {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ ha : a < n, ∃ hb : b < n, G.Adj ⟨a,ha⟩ ⟨b,hb⟩

lemma adjAt_iff_adj {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    adjAt G a.val b.val ↔ G.Adj a b :=
  ⟨fun ⟨_,_,h⟩ ↦ h,fun h ↦ ⟨a.isLt,b.isLt,h⟩⟩

lemma adjAt_symm {n : ℕ} {G : SimpleGraph (Fin n)} {a b : ℕ} (h : adjAt G a b) : adjAt G b a :=
  ⟨h.2.choose,h.choose,h.2.choose_spec.symm⟩

lemma adjAt_ne {n : ℕ} {G : SimpleGraph (Fin n)} {a b : ℕ} (h : adjAt G a b) : a ≠ b := by
  rintro rfl
  obtain ⟨_,_,h⟩ := h
  exact h.ne rfl

/-- The embedding of an interval starting at an offset. -/
def intervalEmb {d m n : ℕ} (h : d+m ≤ n) : Fin (m+1) ↪ Fin (n+1) where
  toFun a := ⟨d+a.val,by have ha := a.isLt; omega⟩
  inj' := by
    intro a b he
    apply Fin.ext
    have hEq : d+a.val = d+b.val := congrArg Fin.val he
    omega

@[simp]
lemma intervalEmb_val {d m n : ℕ} (h : d+m ≤ n) (a : Fin (m+1)) :
    (intervalEmb h a).val = d+a.val := rfl

lemma adjAt_map_intervalEmb {d m n : ℕ} (h : d+m ≤ n) (G : SimpleGraph (Fin (m+1)))
    (a b : ℕ) : adjAt (G.map (intervalEmb h)) a b ↔
      ∃ u w, a = d+u ∧ b = d+w ∧ adjAt G u w := by
  constructor
  · rintro ⟨ha,hb,he⟩
    obtain ⟨u,w,hw,hu',hw'⟩ := (SimpleGraph.map_adj (intervalEmb h) G _ _).mp he
    exact ⟨u.val,w.val,(congrArg Fin.val hu').symm,(congrArg Fin.val hw').symm,
      (adjAt_iff_adj G u w).mpr hw⟩
  · rintro ⟨u,w,rfl,rfl,hu,hw,he⟩
    let a : Fin (m+1) := ⟨u,hu⟩
    let b : Fin (m+1) := ⟨w,hw⟩
    exact ⟨(intervalEmb h a).isLt,(intervalEmb h b).isLt,
      (SimpleGraph.map_adj_apply (f := intervalEmb h)).mpr he⟩

lemma adjAt_map_zero {m n : ℕ} (h : 0+m ≤ n) (G : SimpleGraph (Fin (m+1)))
    (a b : ℕ) : adjAt (G.map (intervalEmb h)) a b ↔ adjAt G a b := by
  rw [adjAt_map_intervalEmb]
  simp only [Nat.zero_add]
  exact ⟨fun ⟨_,_,rfl,rfl,he⟩ ↦ he,fun he ↦ ⟨a,b,rfl,rfl,he⟩⟩

lemma adjAt_sup {n : ℕ} (G H : SimpleGraph (Fin n)) (a b : ℕ) :
    adjAt (G ⊔ H) a b ↔ adjAt G a b ∨ adjAt H a b := by
  constructor
  · rintro ⟨ha,hb,h | h⟩
    · exact Or.inl ⟨ha,hb,h⟩
    · exact Or.inr ⟨ha,hb,h⟩
  · rintro (⟨ha,hb,h⟩ | ⟨ha,hb,h⟩)
    · exact ⟨ha,hb,Or.inl h⟩
    · exact ⟨ha,hb,Or.inr h⟩

/-- The number of steps between the two endpoints in path order. -/
abbrev BasicShape.span (T : BasicShape) : ℕ := T.additionalVertices+1

lemma BasicShape.span_pos (T : BasicShape) : 0 < T.span := Nat.zero_lt_succ _

/-- A chain listed from its rightmost to its leftmost block. -/
abbrev Chain := List BasicShape

namespace Chain

/-- The total number of steps along the spanning path of the chain. -/
def span : Chain → ℕ
  | [] => 0
  | T :: P => span P + T.span

@[simp]
lemma span_nil : span [] = 0 := rfl

@[simp]
lemma span_cons (T : BasicShape) (P : Chain) : span (T::P) = span P + T.span := rfl

lemma span_eq_zero_iff (P : Chain) : span P = 0 ↔ P = [] := by
  cases P with
  | nil => simp
  | cons T P =>
    have h := T.span_pos
    simp only [span_cons,List.cons_ne_nil,iff_false]
    omega

lemma span_append (P Q : Chain) : span (P++Q) = span P+span Q := by
  induction P with
  | nil => simp
  | cons T P ih =>
    simp only [List.cons_append,span_cons,ih]
    omega

/-- The old chain's interval when one appends a block. -/
def prefixEmb (T : BasicShape) (P : Chain) : Fin (span P+1) ↪ Fin (span (T::P)+1) :=
  intervalEmb (show 0+span P ≤ span (T::P) by simp)

/-- The final block's interval. -/
def tailBlock (T : BasicShape) (P : Chain) : Fin (T.span+1) ↪ Fin (span (T::P)+1) :=
  intervalEmb (show span P+T.span ≤ span (T::P) from le_rfl)

/-- The union of the block graphs in their spanning-path intervals. -/
def graph : (P : Chain) → SimpleGraph (Fin (span P+1))
  | [] => ⊥
  | T::P => ((graph P).map (prefixEmb T P)) ⊔ (T.pathGraph.map (tailBlock T P))

/-- The shape of a single chain. The empty chain has coincident boundaries. -/
def toShape (P : Chain) : Shape := ⟨span P+1,graph P,0,Fin.last (span P)⟩

lemma adjAt_cons (T : BasicShape) (P : Chain) (a b : ℕ) :
    adjAt (graph (T::P)) a b ↔ adjAt (graph P) a b ∨
      ∃ u w, a = span P+u ∧ b = span P+w ∧ adjAt T.pathGraph u w := by
  rw [graph,adjAt_sup]
  change (adjAt ((graph P).map (intervalEmb (d := 0) _)) a b ∨
    adjAt (T.pathGraph.map (intervalEmb (d := span P) _)) a b) ↔ _
  rw [adjAt_map_zero,adjAt_map_intervalEmb]

lemma adjAt_succ (P : Chain) {a : ℕ} (h : a+1 ≤ span P) : adjAt (graph P) a (a+1) := by
  induction P with
  | nil => simp only [span_nil] at h; omega
  | cons T P ih =>
    rw [adjAt_cons]
    by_cases ha : a+1 ≤ span P
    · exact Or.inl (ih ha)
    · have h₀ : span P ≤ a := by omega
      have h₁ : a-span P+1 ≤ T.span := by rw [span_cons] at h; omega
      have hu : a-span P < T.additionalVertices+2 := by unfold BasicShape.span at h₁; omega
      have hw : a-span P+1 < T.additionalVertices+2 := by unfold BasicShape.span at h₁; omega
      exact Or.inr ⟨a-span P,a-span P+1,by omega,by omega,hu,hw,T.pathGraph_adj_of_succ rfl⟩

lemma path_le (P : Chain) : SimpleGraph.pathGraph (span P+1) ≤ graph P := by
  intro a b hab
  rw [SimpleGraph.pathGraph_adj] at hab
  rcases hab with h | h
  · apply (adjAt_iff_adj _ _ _).mp
    rw [← h]
    exact adjAt_succ P (by rw [h]; exact Nat.le_of_lt_succ b.isLt)
  · apply (adjAt_iff_adj _ _ _).mp
    apply adjAt_symm
    rw [← h]
    exact adjAt_succ P (by rw [h]; exact Nat.le_of_lt_succ a.isLt)

lemma preconnected (P : Chain) : (graph P).Preconnected :=
  (preconnected_pathGraph _).mono (path_le P)

lemma adjAt_last_endpoints (T : BasicShape) (P : Chain) :
    adjAt (graph (T::P)) (span P) (span (T::P)) :=
  (adjAt_cons _ _ _ _).mpr (Or.inr ⟨0,T.span,Nat.add_zero _,
    rfl,(adjAt_iff_adj T.pathGraph _ _).mpr T.pathGraph_adj_endpoints⟩)

lemma adjAt_no_cross_last_cut (T : BasicShape) (P : Chain) {a b : ℕ}
    (ha : a < span P) (hb : span P < b) : ¬adjAt (graph (T::P)) a b := by
  intro h
  rcases (adjAt_cons _ _ _ _).mp h with ⟨_,h,_⟩ | ⟨u,_,h,_,_⟩
  · omega
  · omega

lemma adjAt_prefix_iff (T : BasicShape) (P : Chain) {a b : ℕ}
    (ha : a ≤ span P) (hb : b ≤ span P) :
    adjAt (graph (T::P)) a b ↔ adjAt (graph P) a b := by
  rw [adjAt_cons]
  refine or_iff_left_of_imp ?_
  rintro ⟨u,w,hu,hw,he⟩
  exact (adjAt_ne he (by omega)).elim

lemma adjAt_tail_iff (T : BasicShape) (P : Chain) (a b : ℕ) :
    adjAt (graph (T::P)) (span P+a) (span P+b) ↔ adjAt T.pathGraph a b := by
  rw [adjAt_cons]
  constructor
  · rintro (h | ⟨u,w,hu,hw,h⟩)
    · have h₁ := h.choose
      have h₂ := h.2.choose
      exact (adjAt_ne h (by omega)).elim
    · simpa only [Nat.add_left_cancel hu,Nat.add_left_cancel hw] using h
  · exact fun h ↦ Or.inr ⟨a,b,rfl,rfl,h⟩

end Chain

end LovaszTheta.Independent
