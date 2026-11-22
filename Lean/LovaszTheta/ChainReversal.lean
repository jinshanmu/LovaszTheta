module

public import LovaszTheta.ClosureRecovery
public import Mathlib.Data.Fin.Rev

/-!
# Reversing chains

Reversing the path reverses the order of the blocks and the
boundaries of each block. The added closing edge is preserved.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

private lemma fin_rev_add_one {n : ℕ} (a : Fin (n+2)) : a.rev+1 = -a := by
  by_cases ha : a = 0
  · subst a
    rw [Fin.rev_zero,neg_zero,← finRotate_apply,finRotate_last]
  have hRev : a.rev ≠ Fin.last (n+1) := by
    intro h
    exact ha (by simpa only [Fin.rev_last] using Fin.rev_eq_iff.mp h)
  rw [← finRotate_apply]
  apply Fin.ext
  rw [coe_finRotate_of_ne_last hRev,Fin.val_neg,ite_eq_right ha,Fin.val_rev]
  have h := a.isLt
  omega

private lemma block_mirror_adj (T : BasicShape) (a b : Fin (T.span+1)) :
    T.reverse.pathGraph.Adj a.rev b.rev ↔ T.pathGraph.Adj a b := by
  change T.graph.Adj (1- -a.rev) (1- -b.rev) ↔ T.graph.Adj (-a) (-b)
  rw [sub_neg_eq_add,sub_neg_eq_add,add_comm 1 a.rev,add_comm 1 b.rev,fin_rev_add_one,fin_rev_add_one]

private lemma block_mirror_adjAt (T : BasicShape) {a b : ℕ} (ha : a ≤ T.span) (hb : b ≤ T.span) :
    adjAt T.reverse.pathGraph (T.span-a) (T.span-b) ↔ adjAt T.pathGraph a b := by
  let u : Fin (T.span+1) := ⟨a,Nat.lt_succ_of_le ha⟩
  let v : Fin (T.span+1) := ⟨b,Nat.lt_succ_of_le hb⟩
  have hu : u.rev.val = T.span-a := by rw [Fin.val_rev]; change T.span+1-(a+1) = _; omega
  have hv : v.rev.val = T.span-b := by rw [Fin.val_rev]; change T.span+1-(b+1) = _; omega
  rw [← hu,← hv]
  exact (adjAt_iff_adj _ u.rev v.rev).trans ((block_mirror_adj T u v).trans (adjAt_iff_adj _ u v).symm)

namespace Chain

lemma adjAt_singleton (T : BasicShape) (a b : ℕ) :
    adjAt (graph [T]) a b ↔ adjAt T.pathGraph a b := by
  rw [adjAt_cons]
  simp only [span_nil,Nat.zero_add]
  constructor
  · rintro (⟨_,_,h⟩ | ⟨_,_,rfl,rfl,h⟩)
    · exact h.elim
    · exact h
  · exact fun h ↦ Or.inr ⟨a,b,rfl,rfl,h⟩

lemma adjAt_append (P Q : Chain) (a b : ℕ) :
    adjAt (graph (P++Q)) a b ↔ adjAt (graph Q) a b ∨
      ∃ u w, a = span Q+u ∧ b = span Q+w ∧ adjAt (graph P) u w := by
  induction P generalizing a b with
  | nil =>
    simp only [List.nil_append]
    exact ⟨Or.inl,fun he ↦ he.elim id (fun ⟨_,_,_,_,_,_,he⟩ ↦ he.elim)⟩
  | cons T P ih =>
    rw [List.cons_append,adjAt_cons,ih]
    constructor
    · rintro ((he | ⟨u,w,ha,hb,he⟩) | ⟨u,w,ha,hb,he⟩)
      · exact Or.inl he
      · exact Or.inr ⟨u,w,ha,hb,(adjAt_cons _ _ _ _).mpr (Or.inl he)⟩
      · refine Or.inr ⟨span P+u,span P+w,?_,?_,(adjAt_cons _ _ _ _).mpr (Or.inr ⟨u,w,rfl,rfl,he⟩)⟩
        · rw [ha,span_append]; omega
        · rw [hb,span_append]; omega
    · rintro (he | ⟨u,w,ha,hb,he⟩)
      · exact Or.inl (Or.inl he)
      · rcases (adjAt_cons _ _ _ _).mp he with he | ⟨i,j,hi,hj,he⟩
        · exact Or.inl (Or.inr ⟨u,w,ha,hb,he⟩)
        · refine Or.inr ⟨i,j,?_,?_,he⟩
          · rw [ha,hi,span_append]; omega
          · rw [hb,hj,span_append]; omega

/-- Reverse the ordered blocks and the orientation of each block. -/
def reversed (P : Chain) : Chain := P.reverse.map BasicShape.reverse

lemma reversed_cons (T : BasicShape) (P : Chain) : reversed (T::P) = reversed P ++ [T.reverse] := by
  simp [reversed]

lemma span_reversed (P : Chain) : span (reversed P) = span P := by
  induction P with
  | nil => rfl
  | cons T P ih =>
    rw [reversed_cons,span_append,ih,span_cons]
    change span P+(0+T.span) = span P+T.span
    rw [Nat.zero_add]

lemma reversed_adjAt (P : Chain) {a b : ℕ} (ha : a ≤ span P) (hb : b ≤ span P) :
    adjAt (graph (reversed P)) (span P-a) (span P-b) ↔ adjAt (graph P) a b := by
  induction P generalizing a b with
  | nil =>
    simp only [span_nil,Nat.zero_sub]
    exact iff_of_false (fun ⟨_,_,he⟩ ↦ he.elim) (fun ⟨_,_,he⟩ ↦ he.elim)
  | cons T P ih =>
    rw [reversed_cons,adjAt_append,adjAt_singleton,adjAt_cons,span_cons]
    change (_ ∨ ∃ u w, _ = (0+T.span)+u ∧ _ = (0+T.span)+w ∧ adjAt (graph (reversed P)) u w) ↔ _
    simp only [Nat.zero_add]
    constructor
    · rintro (he | ⟨u,w,hu,hw,he⟩)
      · have ha' := he.choose
        have hb' := he.2.choose
        change span P+T.span-a < T.span+1 at ha'
        change span P+T.span-b < T.span+1 at hb'
        have ha₀ : a-span P ≤ T.span := by rw [span_cons] at ha; omega
        have hb₀ : b-span P ≤ T.span := by rw [span_cons] at hb; omega
        refine Or.inr ⟨a-span P,b-span P,by omega,by omega,(block_mirror_adjAt T ha₀ hb₀).mp ?_⟩
        rw [show T.span-(a-span P) = span P+T.span-a by omega,
          show T.span-(b-span P) = span P+T.span-b by omega]
        exact he
      · have ha' : a ≤ span P := by
          have ht : a ≤ span P+T.span := ha
          omega
        have hb' : b ≤ span P := by
          have ht : b ≤ span P+T.span := hb
          omega
        refine Or.inl ((ih ha' hb').mp ?_)
        rwa [show span P-a = u by omega,show span P-b = w by omega]
    · rintro (he | ⟨u,w,rfl,rfl,he⟩)
      · have ha' := Nat.le_of_lt_succ he.choose
        have hb' := Nat.le_of_lt_succ he.2.choose
        exact Or.inr ⟨span P-a,span P-b,by omega,by omega,(ih ha' hb').mpr he⟩
      · have hu := Nat.le_of_lt_succ he.choose
        have hw := Nat.le_of_lt_succ he.2.choose
        apply Or.inl
        rw [show span P+T.span-(span P+u) = T.span-u by omega,
          show span P+T.span-(span P+w) = T.span-w by omega]
        exact (block_mirror_adjAt T hu hw).mpr he

private lemma adjAt_closing_edge (P : Chain) (hp : P ≠ []) (a b : ℕ) :
    adjAt (edge (0 : Fin (span P+1)) (Fin.last (span P))) a b ↔
      (a = 0 ∧ b = span P) ∨ (a = span P ∧ b = 0) := by
  have hn := span_pos_of_ne_nil hp
  constructor
  · rintro ⟨ha,hb,he⟩
    rcases ((edge_adj _ _ _ _).mp he).1 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨congrArg Fin.val h₁,congrArg Fin.val h₂⟩
    · exact Or.inr ⟨congrArg Fin.val h₁,congrArg Fin.val h₂⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨by omega,by omega,(edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,fun h ↦
        (Nat.ne_of_lt hn) (congrArg Fin.val h)⟩⟩
    · exact ⟨by omega,by omega,(edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,fun h ↦
        (Nat.ne_of_gt hn) (congrArg Fin.val h)⟩⟩

lemma closedGraph_reversed_adjAt (P : Chain) (hP : P ≠ []) (hR : reversed P ≠ [])
    {a b : ℕ} (ha : a ≤ span P) (hb : b ≤ span P) :
    adjAt (closedGraph (reversed P)) (span P-a) (span P-b) ↔ adjAt (closedGraph P) a b := by
  rw [closedGraph,closedGraph,adjAt_sup,adjAt_sup,reversed_adjAt P ha hb,
    adjAt_closing_edge _ hR,adjAt_closing_edge _ hP,span_reversed]
  apply or_congr_right
  omega

/-- Reversing the ordered chain reverses its basic closure. -/
theorem close_reversed (P : Chain) (hP : P ≠ []) (hR : reversed P ≠ []) :
    (reversed P).close hR = (P.close hP).reverse := by
  have hSize : ((reversed P).close hR).additionalVertices = (P.close hP).reverse.additionalVertices := by
    change span (reversed P)-1 = span P-1
    rw [span_reversed]
  have hS : (P.close hP).span = span P := by
    have h := span_pos_of_ne_nil hP
    change span P-1+1 = span P
    omega
  apply eq_of_path_adjacency hSize
  intro a b
  rw [close_adjAt]
  by_cases ha : a ≤ span P
  · by_cases hb : b ≤ span P
    · have hai : span P-a ≤ (P.close hP).span := by rw [hS]; exact Nat.sub_le _ _
      have hbi : span P-b ≤ (P.close hP).span := by rw [hS]; exact Nat.sub_le _ _
      have h := block_mirror_adjAt (P.close hP) hai hbi
      have hA : span P-(span P-a) = a := by omega
      have hB : span P-(span P-b) = b := by omega
      rw [hS,hA,hB,close_adjAt] at h
      have he := closedGraph_reversed_adjAt P hP hR (Nat.sub_le (span P) a) (Nat.sub_le (span P) b)
      rw [hA,hB] at he
      exact he.trans h.symm
    · exact iff_of_false (fun he ↦ hb (by simpa only [span_reversed] using Nat.le_of_lt_succ he.2.choose))
        (fun he ↦ hb (by have hlt := he.2.choose; change b < (P.close hP).span+1 at hlt; omega))
  · exact iff_of_false (fun he ↦ ha (by simpa only [span_reversed] using Nat.le_of_lt_succ he.choose))
        (fun he ↦ ha (by have hlt := he.choose; change a < (P.close hP).span+1 at hlt; omega))

end Chain

end LovaszTheta.Independent
