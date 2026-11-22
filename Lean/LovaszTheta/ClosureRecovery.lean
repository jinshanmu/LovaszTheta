module

public import LovaszTheta.ChainClosure

/-!
# Recovering the blocks from the closure

After deleting the added edge, the last junction is the final
position that no edge crosses strictly. Recover the last block
and repeat on the preceding chain.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

lemma eq_of_path_adjacency {T U : BasicShape} (hSize : T.additionalVertices = U.additionalVertices)
    (h : ∀ a b, adjAt T.pathGraph a b ↔ adjAt U.pathGraph a b) : T = U := by
  obtain ⟨n,G,hG,hN⟩ := T
  obtain ⟨m,H,hH,hM⟩ := U
  change n = m at hSize
  subst m
  have hEq : G = H := by
    ext a b
    have he := (adjAt_iff_adj _ (-a) (-b)).symm.trans ((h (-a).val (-b).val).trans
      (adjAt_iff_adj _ (-a) (-b)))
    change G.Adj (- -a) (- -b) ↔ H.Adj (- -a) (- -b) at he
    simpa only [neg_neg] using he
  subst H
  rfl

namespace Chain

/-- A graph in spanning-path order, with its size, determines the ordered blocks. -/
theorem eq_of_adjacency (P Q : Chain) (hSize : span P = span Q)
    (h : ∀ a b, adjAt (graph P) a b ↔ adjAt (graph Q) a b) : P = Q := by
  induction P generalizing Q with
  | nil => exact ((span_eq_zero_iff Q).mp hSize.symm).symm
  | cons T P ih =>
    cases Q with
    | nil => exact ((span_eq_zero_iff (T::P)).mp hSize)
    | cons U Q =>
      have hTotal₁ : span P < span (T::P) := by
        have he := T.span_pos
        rw [span_cons]
        omega
      have hTotal₂ : span Q < span (U::Q) := by
        have he := U.span_pos
        rw [span_cons]
        omega
      have hJunction : span P = span Q := by
        apply le_antisymm
        · by_contra! he
          have he' : span P < span (U::Q) := hSize ▸ hTotal₁
          exact adjAt_no_cross_last_cut T P he (hSize.symm ▸ he')
            ((h (span Q) (span (U::Q))).mpr (adjAt_last_endpoints U Q))
        · by_contra! he
          have he' : span Q < span (T::P) := hSize.symm ▸ hTotal₂
          exact adjAt_no_cross_last_cut U Q he (hSize ▸ he')
            ((h (span P) (span (T::P))).mp (adjAt_last_endpoints T P))
      have hT : T.additionalVertices = U.additionalVertices := by
        rw [span_cons,span_cons,hJunction] at hSize
        dsimp only [BasicShape.span] at hSize
        omega
      have hTail : T = U := eq_of_path_adjacency hT fun a b ↦ by
        have he := h (span P+a) (span P+b)
        rw [adjAt_tail_iff,hJunction,adjAt_tail_iff] at he
        exact he
      have hPrefix : P = Q := ih Q hJunction fun a b ↦ by
        by_cases ha : a ≤ span P
        · by_cases hb : b ≤ span P
          · exact (adjAt_prefix_iff T P ha hb).symm.trans
              ((h a b).trans (adjAt_prefix_iff U Q (hJunction ▸ ha) (hJunction ▸ hb)))
          · exact iff_of_false (fun he ↦ hb (Nat.le_of_lt_succ he.2.choose))
              (fun he ↦ hb (hJunction.symm ▸ Nat.le_of_lt_succ he.2.choose))
        · exact iff_of_false (fun he ↦ ha (Nat.le_of_lt_succ he.choose))
            (fun he ↦ ha (hJunction.symm ▸ Nat.le_of_lt_succ he.choose))
      rw [hTail,hPrefix]

lemma no_boundary_edge_of_length_ge_two {P : Chain} (h : 2 ≤ P.length) :
    ¬adjAt (graph P) 0 (span P) := by
  cases P with
  | nil => simp at h
  | cons T P =>
    have hn : P ≠ [] := fun he ↦ by subst P; simp at h
    have hw := span_pos_of_ne_nil hn
    have hz : span P < span (T::P) := by
      have hT := T.span_pos
      rw [span_cons]
      omega
    exact adjAt_no_cross_last_cut T P hw hz

lemma close_adjAt (P : Chain) (h : P ≠ []) (a b : ℕ) :
    adjAt (P.close h).pathGraph a b ↔ adjAt P.closedGraph a b := by
  let e : Fin ((P.close h).additionalVertices+2) ≃ Fin (span P+1) := finCongr (closure_size P h)
  constructor
  · rintro ⟨ha,hb,he⟩
    let u : Fin ((P.close h).additionalVertices+2) := ⟨a,ha⟩
    let w : Fin ((P.close h).additionalVertices+2) := ⟨b,hb⟩
    have he' : (P.close h).pathGraph.Adj (e.symm (e u)) (e.symm (e w)) := by
      rw [e.symm_apply_apply u,e.symm_apply_apply w]
      exact he
    exact ⟨(e u).isLt,(e w).isLt,(close_pathGraph_adj P h (e u) (e w)).mp he'⟩
  · rintro ⟨ha,hb,he⟩
    let u : Fin (span P+1) := ⟨a,ha⟩
    let w : Fin (span P+1) := ⟨b,hb⟩
    exact ⟨(e.symm u).isLt,(e.symm w).isLt,(close_pathGraph_adj P h u w).mpr he⟩

private lemma adjAt_eq_of_closed_adjAt {P Q : Chain} (hp : 2 ≤ P.length)
    (hSize : span P = span Q) {a b : ℕ}
    (he : adjAt P.closedGraph a b ↔ adjAt Q.closedGraph a b)
    (h : adjAt (graph P) a b) : adjAt (graph Q) a b := by
  rw [closedGraph,closedGraph,adjAt_sup,adjAt_sup] at he
  rcases he.mp (Or.inl h) with h' | ⟨ha,hb,hEdge⟩
  · exact h'
  · rcases ((edge_adj _ _ _ _).mp hEdge).1 with ⟨ha',hb'⟩ | ⟨ha',hb'⟩
    · have hA : a = 0 := congrArg Fin.val ha'
      have hB : b = span Q := congrArg Fin.val hb'
      subst a
      rw [hB,← hSize] at h
      exact (no_boundary_edge_of_length_ge_two hp h).elim
    · have hA : a = span Q := congrArg Fin.val ha'
      have hB : b = 0 := congrArg Fin.val hb'
      subst b
      rw [hA,← hSize] at h
      exact (no_boundary_edge_of_length_ge_two hp (adjAt_symm h)).elim

/-- Adding the boundary edge is injective on ordered chains of at least two blocks. -/
theorem close_injective {P Q : Chain} (hp : 2 ≤ P.length) (hq : 2 ≤ Q.length)
    (hp' : P ≠ []) (hq' : Q ≠ []) (he : P.close hp' = Q.close hq') : P = Q := by
  have hP := span_pos_of_ne_nil hp'
  have hQ := span_pos_of_ne_nil hq'
  have hSize := congrArg BasicShape.additionalVertices he
  change span P-1 = span Q-1 at hSize
  have hSize' : span P = span Q := by omega
  apply eq_of_adjacency P Q hSize'
  intro a b
  have h := (close_adjAt P hp' a b).symm.trans ((by rw [he] :
    adjAt (P.close hp').pathGraph a b ↔ adjAt (Q.close hq').pathGraph a b).trans (close_adjAt Q hq' a b))
  exact ⟨adjAt_eq_of_closed_adjAt hp hSize' h,adjAt_eq_of_closed_adjAt hq hSize'.symm h.symm⟩

end Chain

end LovaszTheta.Independent
