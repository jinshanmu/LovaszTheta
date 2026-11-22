module

public import LovaszTheta.ChainIntervals

/-!
# Single chains and separated chain pairs

A term has a right chain and, when present, a disjoint left chain.
The old term is a prefix of the interval when a block is appended.
The boundary and incidence statements also cover chains of length zero.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

/-- A single chain, or two separated chains, with their external boundaries. -/
structure ChainTerm where
  /-- The independent left component in a pair. -/
  leftChain : Option Chain
  /-- The chain ending at the right boundary. -/
  rightChain : Chain

namespace ChainTerm

/-- A single chain. -/
abbrev single (P : Chain) : ChainTerm := ⟨none,P⟩

/-- A pair of disjoint chains. -/
abbrev pair (P Q : Chain) : ChainTerm := ⟨some P,Q⟩

/-- Position of the left endpoint of the right chain. -/
abbrev offset (P : ChainTerm) : ℕ := P.leftChain.elim 0 (fun Q ↦ Chain.span Q+1)

/-- The position of the right boundary. -/
abbrev span (P : ChainTerm) : ℕ := Chain.span P.rightChain + P.offset

/-- The number of extra components in the normalization. -/
def extra (P : ChainTerm) : ℕ := P.leftChain.elim 0 (fun _ ↦ 1)

/-- Append a block to the right chain. -/
def append (P : ChainTerm) (T : BasicShape) : ChainTerm := ⟨P.leftChain,T::P.rightChain⟩

@[simp]
lemma span_append (P : ChainTerm) (T : BasicShape) : (P.append T).span = P.span+T.span := by
  simp only [span,offset,append,Chain.span_cons]
  omega

/-- The old term's vertices in the enlarged term. -/
def prefixEmb (P : ChainTerm) (T : BasicShape) : Fin (P.span+1) ↪ Fin ((P.append T).span+1) :=
  intervalEmb (show 0+P.span ≤ (P.append T).span by simp)

/-- The appended block's vertices in the enlarged term. -/
def tailEmb (P : ChainTerm) (T : BasicShape) : Fin (T.span+1) ↪ Fin ((P.append T).span+1) :=
  intervalEmb (span_append P T).ge

/-- The graph with the right chain translated past the left chain, if present. -/
def graph (P : ChainTerm) : SimpleGraph (Fin (P.span+1)) where
  Adj a b := (∃ L, P.leftChain = some L ∧ adjAt (Chain.graph L) a.val b.val) ∨
    ∃ u w, a.val = P.offset+u ∧ b.val = P.offset+w ∧ adjAt (Chain.graph P.rightChain) u w
  symm := ⟨fun _ _ h ↦ by
    rcases h with ⟨L,hL,h⟩ | ⟨u,w,hu,hw,h⟩
    · exact Or.inl ⟨L,hL,adjAt_symm h⟩
    · exact Or.inr ⟨w,u,hw,hu,adjAt_symm h⟩⟩
  loopless := ⟨fun _ h ↦ by
    rcases h with ⟨_,_,h⟩ | ⟨u,w,hu,hw,h⟩
    · exact adjAt_ne h rfl
    · exact adjAt_ne h (Nat.add_left_cancel (hu.symm.trans hw))⟩

/-- The graph and its outer boundaries. -/
abbrev toShape (P : ChainTerm) : Shape := ⟨P.span+1,P.graph,0,Fin.last P.span⟩

/-- The normalized matrix of a single chain or a pair of disjoint chains. -/
noncomputable def matrix (P : ChainTerm) {n : ℕ} (x : EdgeIndex (Fin n) → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)^(-((P.span : ℝ)+P.extra)/2) • graphMatrix P.toShape x

lemma adjAt_iff (P : ChainTerm) (a b : ℕ) :
    adjAt P.graph a b ↔ (∃ L, P.leftChain = some L ∧ adjAt (Chain.graph L) a b) ∨
      ∃ u w, a = P.offset+u ∧ b = P.offset+w ∧ adjAt (Chain.graph P.rightChain) u w := by
  constructor
  · rintro ⟨_,_,h⟩
    exact h
  · rintro (⟨L,hL,h⟩ | ⟨u,w,rfl,rfl,h⟩)
    · have h₁ := h.choose
      have h₂ := h.2.choose
      have hBound : Chain.span L ≤ P.span := by
        change Chain.span L ≤ Chain.span P.rightChain + P.leftChain.elim 0 (fun Q ↦ Chain.span Q+1)
        rw [hL]
        simp only [Option.elim_some]
        omega
      exact ⟨by omega,by omega,Or.inl ⟨L,hL,h⟩⟩
    · have h₁ := h.choose
      have h₂ := h.2.choose
      exact ⟨by change P.offset+u < Chain.span P.rightChain+P.offset+1; omega,
        by change P.offset+w < Chain.span P.rightChain+P.offset+1; omega,Or.inr ⟨u,w,rfl,rfl,h⟩⟩

lemma adjAt_append (P : ChainTerm) (T : BasicShape) (a b : ℕ) :
    adjAt (P.append T).graph a b ↔ adjAt P.graph a b ∨
      ∃ u w, a = P.span+u ∧ b = P.span+w ∧ adjAt T.pathGraph u w := by
  rw [adjAt_iff,adjAt_iff]
  simp only [append,offset,Chain.adjAt_cons]
  constructor
  · rintro (h | ⟨u,w,rfl,rfl,h | he⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨u,w,rfl,rfl,h⟩)
    · obtain ⟨i,j,rfl,rfl,he⟩ := he
      exact Or.inr ⟨i,j,by simp only [span,offset]; omega,by simp only [span,offset]; omega,he⟩
  · rintro ((h | ⟨u,w,rfl,rfl,h⟩) | ⟨u,w,rfl,rfl,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u,w,rfl,rfl,Or.inl h⟩
    · exact Or.inr ⟨Chain.span P.rightChain+u,Chain.span P.rightChain+w,
        by simp only [span,offset]; omega,by simp only [span,offset]; omega,Or.inr ⟨u,w,rfl,rfl,h⟩⟩

lemma graph_append (P : ChainTerm) (T : BasicShape) :
    (P.append T).graph = (P.graph.map (P.prefixEmb T)) ⊔ (T.pathGraph.map (P.tailEmb T)) := by
  ext a b
  rw [← adjAt_iff_adj,← adjAt_iff_adj,adjAt_append,adjAt_sup]
  change _ ↔ adjAt (P.graph.map (intervalEmb (d := 0) _)) a.val b.val ∨
    adjAt (T.pathGraph.map (intervalEmb (d := P.span) _)) a.val b.val
  rw [adjAt_map_zero,adjAt_map_intervalEmb]

lemma graph_single (P : Chain) :
    (single P).graph = Chain.graph P := by
  ext a b
  have he : adjAt (single P).graph a.val b.val ↔ adjAt (Chain.graph P) a.val b.val := by
    rw [adjAt_iff]
    simp only [single,offset,reduceCtorEq,false_and,exists_false,false_or,Option.elim_none,Nat.zero_add]
    exact ⟨fun ⟨_,_,rfl,rfl,h⟩ ↦ h,fun h ↦ ⟨a.val,b.val,rfl,rfl,h⟩⟩
  exact (adjAt_iff_adj _ _ _).symm.trans (he.trans (adjAt_iff_adj _ _ _))

lemma no_cross_components (P : ChainTerm) {a b : Fin (P.span+1)} (he : P.graph.Adj a b) :
    a.val < P.offset ↔ b.val < P.offset := by
  rcases (P.adjAt_iff _ _).mp ((adjAt_iff_adj _ _ _).mpr he) with ⟨L,hL,h⟩ | ⟨u,w,hu,hw,_⟩
  · have h₁ := h.choose
    have h₂ := h.2.choose
    unfold offset
    simp only [hL,Option.elim_some]
    exact iff_of_true h₁ h₂
  · exact iff_of_false (by omega) (by omega)

lemma offset_eq_zero_iff (P : ChainTerm) : P.offset = 0 ↔ P.leftChain = none := by
  cases hp : P.leftChain <;> simp [offset,hp]

lemma reachable_rightBoundary (P : ChainTerm) {u : Fin (P.span+1)} (hu : P.offset ≤ u.val) :
    P.graph.Reachable u (Fin.last P.span) := by
  let g := (Chain.graph P.rightChain).map (intervalEmb (d := P.offset) (n := P.span) (Nat.add_comm _ _).le)
  let e := intervalEmb (d := P.offset) (n := P.span) (m := Chain.span P.rightChain) (Nat.add_comm _ _).le
  have hu' : u.val-P.offset < Chain.span P.rightChain+1 := by
    have h := u.isLt
    unfold span at h
    omega
  let i : Fin (Chain.span P.rightChain+1) := ⟨u.val-P.offset,hu'⟩
  have hi : e i = u := Fin.ext (Nat.add_sub_of_le hu)
  have hj : e (Fin.last (Chain.span P.rightChain)) = Fin.last P.span := Fin.ext (Nat.add_comm _ _)
  have hReach := (Chain.preconnected P.rightChain i (Fin.last _)).map (SimpleGraph.Embedding.map e (Chain.graph P.rightChain)).toHom
  change g.Reachable (e i) (e (Fin.last _)) at hReach
  rw [hi,hj] at hReach
  apply hReach.mono
  intro a b h
  obtain ⟨u,w,he,hu,hw⟩ := (SimpleGraph.map_adj e (Chain.graph P.rightChain) _ _).mp h
  exact Or.inr ⟨u.val,w.val,(congrArg Fin.val hu).symm,(congrArg Fin.val hw).symm,
    (adjAt_iff_adj _ _ _).mpr he⟩

lemma not_reachable_left_right_pair (P : ChainTerm) (h : P.leftChain.isSome) :
    ¬P.graph.Reachable (0 : Fin (P.span+1)) (Fin.last P.span) := by
  have hOff : 0 < P.offset := by
    cases hp : P.leftChain with
    | none => simp [hp] at h
    | some L => simp [offset,hp]
  intro hReach
  rw [SimpleGraph.reachable_iff_reflTransGen] at hReach
  have hPres {u v : Fin (P.span+1)} (he : Relation.ReflTransGen P.graph.Adj u v)
      (hu : u.val < P.offset) : v.val < P.offset := by
    induction he with
    | refl => exact hu
    | tail h₁ hAdj ih => exact (P.no_cross_components hAdj).mp ih
  have hFin := hPres hReach (by exact hOff)
  change P.span < P.offset at hFin
  unfold span at hFin
  omega

lemma incident_of_not_boundaries (P : ChainTerm) (u : Fin (P.span+1))
    (hLeft : u ≠ 0) (hRight : u ≠ Fin.last P.span) : ∃ w, P.graph.Adj u w := by
  by_cases h : u.val < P.offset
  · have hL : P.leftChain.isSome := by
      cases hp : P.leftChain with
      | none => simp [offset,hp] at h
      | some L => rfl
    obtain ⟨L,hL⟩ := Option.isSome_iff_exists.mp hL
    have hPos : 0 < u.val := Fin.pos_iff_ne_zero.mpr hLeft
    have hBound : (u.val-1)+1 ≤ Chain.span L := by
      simp only [offset,hL,Option.elim_some] at h
      omega
    let w : Fin (P.span+1) := ⟨u.val-1,by have hu := u.isLt; omega⟩
    refine ⟨w,(adjAt_iff_adj _ _ _).mp ((P.adjAt_iff _ _).mpr (Or.inl ⟨L,hL,?_⟩))⟩
    apply adjAt_symm
    have he := Chain.adjAt_succ L hBound
    simpa only [w,show u.val-1+1 = u.val by omega] using he
  · have hLo : P.offset ≤ u.val := Nat.le_of_not_gt h
    have hUp : u.val < P.span := lt_of_le_of_ne (Fin.le_last u) (fun he ↦ hRight (Fin.ext he))
    let w : Fin (P.span+1) := ⟨u.val+1,by omega⟩
    refine ⟨w,(adjAt_iff_adj _ _ _).mp ((P.adjAt_iff _ _).mpr (Or.inr <| ?_))⟩
    refine ⟨u.val-P.offset,u.val-P.offset+1,by omega,by change u.val+1 = _; omega,?_⟩
    apply Chain.adjAt_succ
    unfold span at hUp
    omega

end ChainTerm

end LovaszTheta.Independent
