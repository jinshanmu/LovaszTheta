module

public import LovaszTheta.ChainIntervals
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Closing a chain

An added boundary edge closes the spanning path. The remaining
edges stay in their block intervals, so the new cycle has no
crossing chords.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

lemma noncrossing_adjAt {n : ℕ} {G : SimpleGraph (Fin n)} (hG : Noncrossing G)
    {a u b v : ℕ} (hau : a < u) (hub : u < b) (hbv : b < v) (hab : adjAt G a b) :
    ¬ adjAt G u v := by
  rintro ⟨hu,hv,huv⟩
  obtain ⟨ha,hb,hab⟩ := hab
  exact hG (a := ⟨a,ha⟩) (u := ⟨u,hu⟩) (b := ⟨b,hb⟩) (v := ⟨v,hv⟩) hau hub hbv hab huv

lemma cycleGraph_le_path_sup_edge (n : ℕ) :
    cycleGraph (n+2) ≤ pathGraph (n+2) ⊔ edge 0 (Fin.last (n+1)) := by
  have hOrd (a b : Fin (n+2)) (hOrd : a ≤ b) (he : (cycleGraph (n+2)).Adj a b) :
      (pathGraph (n+2) ⊔ edge 0 (Fin.last (n+1))).Adj a b := by
    have hl : a < b := lt_of_le_of_ne hOrd he.ne
    rcases cycleGraph_adj'.mp he with h | h
    · have hc := Fin.intCast_val_sub_eq_sub_add_ite a b
      rw [h,ite_eq_right (not_le_of_gt hl)] at hc
      have ha := a.isLt
      have hb := b.isLt
      have hA : a = 0 := Fin.ext (by change a.val = 0; omega)
      have hB : b = Fin.last (n+1) := Fin.ext (by change b.val = n+1; omega)
      exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨hA,hB⟩,he.ne⟩)
    · rw [Fin.sub_val_of_le hOrd] at h
      have hl' : a.val < b.val := hl
      exact Or.inl (pathGraph_adj.mpr (Or.inl (by omega)))
  intro a b he
  rcases le_total a b with h | h
  · exact hOrd a b h he
  · exact (hOrd b a h he.symm).symm

namespace Chain

theorem graph_noncrossing (P : Chain) : Noncrossing (graph P) := by
  induction P with
  | nil => exact fun _ _ _ h ↦ h.elim
  | cons T P ih =>
    intro a u b v hau hub hbv hab huv
    have h₁ : a.val < u.val := hau
    have h₂ : u.val < b.val := hub
    have h₃ : b.val < v.val := hbv
    have hA := (adjAt_cons T P _ _).mp ((adjAt_iff_adj _ _ _).mpr hab)
    have hB := (adjAt_cons T P _ _).mp ((adjAt_iff_adj _ _ _).mpr huv)
    rcases hA with hA | ⟨a',b',ha,hb,hA⟩ <;> rcases hB with hB | ⟨u',v',hu,hv,hB⟩
    · exact noncrossing_adjAt ih h₁ h₂ h₃ hA hB
    · have hBound := hA.2.choose
      omega
    · have hBound := hB.2.choose
      omega
    · exact noncrossing_adjAt T.pathGraph_noncrossing (by omega) (by omega) (by omega) hA hB

/-- The spanning path with the added boundary edge, in path coordinates. -/
def closedGraph (P : Chain) : SimpleGraph (Fin (span P+1)) :=
  graph P ⊔ edge 0 (Fin.last (span P))

lemma closedGraph_noncrossing (P : Chain) : Noncrossing (closedGraph P) := by
  intro a u b v hau hub hbv hab huv
  have h₁ : a.val < u.val := hau
  have h₂ : u.val < b.val := hub
  have h₃ : b.val < v.val := hbv
  have hV := v.isLt
  have hNoA : ¬(edge 0 (Fin.last (span P))).Adj a b := by
    rw [edge_adj]
    rintro ⟨⟨ha,hb⟩ | ⟨ha,hb⟩,_⟩
    · have he : b.val = span P := congrArg Fin.val hb
      omega
    · have he : b.val = 0 := congrArg Fin.val hb
      omega
  have hNoB : ¬(edge 0 (Fin.last (span P))).Adj u v := by
    rw [edge_adj]
    rintro ⟨⟨hu,hv⟩ | ⟨hu,hv⟩,_⟩
    · have he : u.val = 0 := congrArg Fin.val hu
      omega
    · have he : v.val = 0 := congrArg Fin.val hv
      omega
  exact (graph_noncrossing P) hau hub hbv (hab.resolve_right hNoA) (huv.resolve_right hNoB)

lemma span_pos_of_ne_nil {P : Chain} (h : P ≠ []) : 0 < span P :=
  Nat.pos_of_ne_zero (fun he ↦ h ((span_eq_zero_iff P).mp he))

/-- The equality aligning path order with the vertex count of the basic closure. -/
lemma closure_size (P : Chain) (h : P ≠ []) : (span P-1)+2 = span P+1 := by
  have he := span_pos_of_ne_nil h
  omega

private lemma noncrossing_cast {m n : ℕ} (h : m = n) {G : SimpleGraph (Fin n)} (he : Noncrossing G) :
    Noncrossing (G.comap (finCongr h)) := by
  subst n
  exact he

/-- The basic shape obtained by closing a nonempty chain and orienting the boundary edge. -/
def close (P : Chain) (h : P ≠ []) : BasicShape where
  additionalVertices := span P-1
  graph := ((closedGraph P).comap (finCongr (closure_size P h))).comap (fun i ↦ -i)
  cycle_le := by
    have hCycle (n : ℕ) (H : SimpleGraph (Fin (n+2))) (h₁ : pathGraph (n+2) ≤ H)
        (h₂ : H.Adj 0 (Fin.last (n+1))) : cycleGraph (n+2) ≤ H := by
      apply (cycleGraph_le_path_sup_edge n).trans
      exact sup_le h₁ ((edge_le_iff H).mpr (Or.inr h₂))
    let e := finCongr (closure_size P h)
    have hBase : cycleGraph ((span P-1)+2) ≤ (closedGraph P).comap e := by
      apply hCycle
      · intro a b hab
        by_cases hab' : (pathGraph (span P+1)).Adj (e a) (e b)
        · exact Or.inl (P.path_le hab')
        · exact (hab' (by
            have he := pathGraph_adj.mp hab
            exact pathGraph_adj.mpr he)).elim
      · have hn : e 0 ≠ e (Fin.last (span P-1+1)) := by
          intro he
          have hv := congrArg Fin.val (e.injective he)
          change 0 = span P-1+1 at hv
          omega
        exact Or.inr ((edge_adj _ _ _ _).mpr
          ⟨Or.inl ⟨Fin.ext rfl,Fin.ext (by have he := span_pos_of_ne_nil h; change span P-1+1 = span P; omega)⟩,hn⟩)
    intro a b he
    apply hBase
    rw [cycleGraph_adj,show -a- -b = b-a by abel,show -b- -a = a-b by abel,or_comm]
    exact cycleGraph_adj.mp he
  noncrossing := by
    intro a u b v
    exact @Noncrossing.comap_neg _ _ (noncrossing_cast (closure_size P h) (closedGraph_noncrossing P)) a u b v

lemma close_pathGraph_adj (P : Chain) (h : P ≠ []) (a b : Fin (span P+1)) :
    (P.close h).pathGraph.Adj ((finCongr (closure_size P h)).symm a) ((finCongr (closure_size P h)).symm b) ↔
      P.closedGraph.Adj a b := by
  let e := finCongr (closure_size P h)
  change P.closedGraph.Adj (e (- -(e.symm a))) (e (- -(e.symm b))) ↔ _
  rw [neg_neg,neg_neg,e.apply_symm_apply,e.apply_symm_apply]

end Chain

end LovaszTheta.Independent
