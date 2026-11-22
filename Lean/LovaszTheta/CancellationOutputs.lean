module

public import LovaszTheta.ExactLastCancellation
public import LovaszTheta.IsolatedExtension

/-!
# The outputs of exact cancellation

Backtracking retains the junction as the right boundary. The
other orientation gives a new isolated right boundary when the
old term was a single chain or the right component had one block.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

private def appendIsolatedEmb {V : Type*} {m : ℕ}
    (e : Fin (m+1) ↪ V) (w : V) (hw : w ∉ Set.range e) : Fin (m+2) ↪ V where
  toFun j := if h : j.val < m+1 then e ⟨j.val,h⟩ else w
  inj' := by
    intro a b he
    change (if h : a.val < m+1 then e ⟨a.val,h⟩ else w) =
      (if h : b.val < m+1 then e ⟨b.val,h⟩ else w) at he
    split_ifs at he with hA hB
    · exact Fin.ext (congrArg (fun i : Fin (m+1) ↦ i.val) (e.injective he))
    · exact (hw ⟨_,he⟩).elim
    · exact (hw ⟨_,he.symm⟩).elim
    · apply Fin.ext
      have ha := a.isLt
      have hb := b.isLt
      omega

private lemma appendIsolatedEmb_castSucc {V : Type*} {m : ℕ}
    (e : Fin (m+1) ↪ V) (w : V) (hw : w ∉ Set.range e) (u : Fin (m+1)) :
    appendIsolatedEmb e w hw u.castSucc = e u := by
  change (if h : u.val < m+1 then e ⟨u.val,h⟩ else w) = _
  rw [dite_eq_left u.isLt]

private lemma appendIsolatedEmb_last {V : Type*} {m : ℕ}
    (e : Fin (m+1) ↪ V) (w : V) (hw : w ∉ Set.range e) :
    appendIsolatedEmb e w hw (Fin.last (m+1)) = w := by
  change (if h : m+1 < m+1 then e ⟨m+1,h⟩ else w) = _
  rw [dite_eq_right (Nat.lt_irrefl _)]

private lemma map_swap_of_isolated {V : Type*} [DecidableEq V] (G : SimpleGraph V) {a b : V}
    (ha : ¬Incident G a) (hb : ¬Incident G b) :
    G.map (Equiv.swap a b).toEmbedding = G := by
  rw [← SimpleGraph.comap_symm]
  ext u v
  change G.Adj (Equiv.swap a b u) (Equiv.swap a b v) ↔ G.Adj u v
  by_cases hu : u = a ∨ u = b
  · rcases hu with rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact iff_of_false (fun h ↦ hb ⟨_,h⟩) (fun h ↦ ha ⟨_,h⟩)
    · rw [Equiv.swap_apply_right]
      exact iff_of_false (fun h ↦ ha ⟨_,h⟩) (fun h ↦ hb ⟨_,h⟩)
  by_cases hv : v = a ∨ v = b
  · rcases hv with rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact iff_of_false (fun h ↦ hb ⟨_,h.symm⟩) (fun h ↦ ha ⟨_,h.symm⟩)
    · rw [Equiv.swap_apply_right]
      exact iff_of_false (fun h ↦ ha ⟨_,h.symm⟩) (fun h ↦ hb ⟨_,h.symm⟩)
  rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ hu (Or.inl h)) (fun h ↦ hu (Or.inr h)),
    Equiv.swap_apply_of_ne_of_ne (fun h ↦ hv (Or.inl h)) (fun h ↦ hv (Or.inr h))]

namespace ChainTerm

private def pairLeftEmb (C : Chain) : Fin (Chain.span C+1) ↪ Fin ((pair C []).span+1) :=
  intervalEmb (d := 0) (by change 0+Chain.span C ≤ 0+(Chain.span C+1); omega)

private lemma pair_empty_graph (C : Chain) :
    (pair C []).graph = (Chain.graph C).map (pairLeftEmb C) := by
  ext a b
  have he := (adjAt_iff (pair C []) a.val b.val)
  simp only [pair,offset,Option.elim_some] at he
  have he' : ((∃ L : Chain, some C = some L ∧ adjAt (Chain.graph L) a.val b.val) ∨
       (∃ u w, a.val = Chain.span C+1+u ∧ b.val = Chain.span C+1+w ∧ adjAt (Chain.graph []) u w)) ↔
      adjAt (Chain.graph C) a.val b.val := by
    constructor
    · rintro (⟨L,hL,h⟩ | ⟨_,_,_,_,_,_,h⟩)
      · exact (Option.some.inj hL).symm ▸ h
      · exact h.elim
    · exact fun h ↦ Or.inl ⟨C,rfl,h⟩
  apply (adjAt_iff_adj _ _ _).symm.trans
  apply he.trans
  apply he'.trans
  have hMap := adjAt_map_zero (show 0+Chain.span C ≤ (pair C []).span by
    change 0+Chain.span C ≤ 0+(Chain.span C+1); omega) (Chain.graph C) a.val b.val
  exact hMap.symm.trans (adjAt_iff_adj _ _ _)

variable (P : ChainTerm) (T S : BasicShape)
variable (p : Identification (P.append T).toShape S.toShape)

/-- The surviving term if an exact cancellation has zero net power. -/
noncomputable def cancellationOutput : Option ChainTerm :=
  if p.outputRight = P.junction T S p then some P
  else if P.leftChain = none then some (pair P.rightChain [])
  else if P.rightChain = [] then some P else none

private lemma embed_with_added_right (h : p.newGraph = P.lastGraph T S p)
    (hW : p.outputRight ≠ P.junction T S p) (hP : P.leftChain = none) :
    ∃ e : Fin (pair P.rightChain []).toShape.vertexCount ↪ p.Vertex,
      p.remaining = (pair P.rightChain []).graph.map e ∧
      e (pair P.rightChain []).toShape.left = p.outputLeft ∧
      e (pair P.rightChain []).toShape.right = p.outputRight := by
  obtain ⟨L,C⟩ := P
  change L = none at hP
  subst L
  let f : Fin (Chain.span C+1) ↪ p.Vertex := (single C).prefixInQuotient T S p
  let ew : p.outputRight ∉ Set.range f := (single C).outputRight_not_in_prefix T S p h hW
  let B := pair C []
  have hSize : B.toShape.vertexCount = Chain.span C+2 := by simp [B,span,offset,Nat.add_assoc]
  let E := finCongr hSize
  let g := appendIsolatedEmb (m := Chain.span C) f p.outputRight ew
  let e := E.toEmbedding.trans g
  refine ⟨e,?_,?_,?_⟩
  · rw [(single C).remaining_eq_prefix_of_exact T S p h,pair_empty_graph,SimpleGraph.map_map,graph_single]
    apply congrArg (fun k ↦ (Chain.graph C).map k)
    funext i
    have hFi : E (pairLeftEmb C i) = i.castSucc := Fin.ext (Nat.zero_add _)
    change f i = g (E (pairLeftEmb C i))
    rw [hFi]
    exact (appendIsolatedEmb_castSucc f p.outputRight ew i).symm
  · have he : E B.toShape.left = (0 : Fin (Chain.span C+1)).castSucc := Fin.ext rfl
    change g (E B.toShape.left) = p.outputLeft
    rw [he]
    exact (appendIsolatedEmb_castSucc f p.outputRight ew _).trans ((single C).prefix_left_eq_output T S p)
  · have he : E B.toShape.right = Fin.last (Chain.span C+1) := Fin.ext (Nat.zero_add _)
    change g (E B.toShape.right) = p.outputRight
    rw [he]
    exact appendIsolatedEmb_last f p.outputRight ew

private lemma embed_with_replaced_right (h : p.newGraph = P.lastGraph T S p)
    (hW : p.outputRight ≠ P.junction T S p) (hL : P.leftChain ≠ none) (hP : P.rightChain = []) :
    ∃ e : Fin P.toShape.vertexCount ↪ p.Vertex, p.remaining = P.graph.map e ∧
      e P.toShape.left = p.outputLeft ∧ e P.toShape.right = p.outputRight := by
  let J := P.junction T S p
  let f := P.prefixInQuotient T S p
  let g := (Equiv.swap J p.outputRight).toEmbedding
  have hR := P.remaining_eq_prefix_of_exact T S p h
  have hJ : ¬Incident p.remaining J := by
    rw [hR]
    change ¬ Incident (P.graph.map f) (P.junction T S p)
    rw [← P.prefix_right_eq_junction T S p]
    rintro ⟨w,he⟩
    obtain ⟨a,b,hab,ha,_⟩ := (SimpleGraph.map_adj f _ _ _).mp he
    exact P.not_incident_right_of_empty hP ⟨b,f.injective ha ▸ hab⟩
  have hW' : ¬Incident p.remaining p.outputRight := by
    rw [hR]
    rintro ⟨v,hv⟩
    obtain ⟨a,_,_,ha,_⟩ := (SimpleGraph.map_adj f _ _ _).mp hv
    exact P.outputRight_not_in_prefix T S p h hW ⟨a,ha⟩
  refine ⟨f.trans g,?_,?_,?_⟩
  · have he := map_swap_of_isolated p.remaining hJ hW'
    rw [hR,SimpleGraph.map_map] at he
    rw [hR]
    exact he.symm
  · change Equiv.swap J p.outputRight (f P.toShape.left) = p.outputLeft
    rw [show f P.toShape.left = p.outputLeft from P.prefix_left_eq_output T S p]
    have hA : p.outputLeft ≠ J := fun h' ↦ hL ((P.offset_eq_zero_iff).mp (by
      have hr := (P.junction_eq_left_iff T S p).mp h'.symm
      change Chain.span P.rightChain+P.offset = 0 at hr
      omega))
    have hB : p.outputLeft ≠ p.outputRight := fun he ↦
      P.outputRight_not_in_prefix T S p h hW ⟨_,(P.prefix_left_eq_output T S p).trans he⟩
    exact Equiv.swap_apply_of_ne_of_ne hA hB
  · change Equiv.swap J p.outputRight (f P.toShape.right) = p.outputRight
    rw [show f P.toShape.right = J from P.prefix_right_eq_junction T S p,Equiv.swap_apply_left]

/-- The retained chain term embeds in the quotient and contains all surviving edges. -/
theorem exists_output_embedding (h : p.newGraph = P.lastGraph T S p) {Q : ChainTerm}
    (hq : P.cancellationOutput T S p = some Q) :
    ∃ e : Fin Q.toShape.vertexCount ↪ p.Vertex, p.remaining = Q.graph.map e ∧
      e Q.toShape.left = p.outputLeft ∧ e Q.toShape.right = p.outputRight := by
  unfold cancellationOutput at hq
  split_ifs at hq with hW hL hE
  · injection hq with he
    subst Q
    exact ⟨P.prefixInQuotient T S p,P.remaining_eq_prefix_of_exact T S p h,
      P.prefix_left_eq_output T S p,(P.prefix_right_eq_junction T S p).trans hW.symm⟩
  · injection hq with he
    subst Q
    exact P.embed_with_added_right T S p h hW hL
  · injection hq with he
    subst Q
    exact P.embed_with_replaced_right T S p h hW hL hE

/-- The exact isolated-vertex factor of an admissible last-block cancellation. -/
theorem graphMatrix_eq_output (h : p.newGraph = P.lastGraph T S p) {Q : ChainTerm}
    (hq : P.cancellationOutput T S p = some Q) {n : ℕ} (x : EdgeIndex (Fin n) → Bool) :
    graphMatrix p.shape x =
      (((n-Q.toShape.vertexCount).descFactorial (p.shape.vertexCount-Q.toShape.vertexCount) : ℕ) : ℝ) •
        graphMatrix Q.toShape x := by
  obtain ⟨e,hG,hL,hR⟩ := P.exists_output_embedding T S p h hq
  have he : p.shape.graph = Q.graph.map (e.trans p.numbering.toEmbedding) := by
    change p.remaining.comap p.numbering.symm.toEmbedding = _
    rw [SimpleGraph.comap_symm p.remaining p.numbering,hG,SimpleGraph.map_map]
    rfl
  have hm := graphMatrix_eq_descFactorial_smul (e.trans p.numbering.toEmbedding)
    he (by exact (congrArg p.numbering hL).trans p.numbered_left)
    (by exact (congrArg p.numbering hR).trans p.numbered_right) x
  simpa only [Fintype.card_fin] using hm

end ChainTerm

end LovaszTheta.Independent
