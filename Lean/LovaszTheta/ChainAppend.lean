module

public import LovaszTheta.LastBlockCancellation

/-!
# Appending a block

The identification with just the common boundary is unique.
It has no canceled edges and its quotient is the enlarged chain
or chain pair.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

lemma map_sup_embedding {A B : Type*} (e : A ↪ B) (G H : SimpleGraph A) :
    (G ⊔ H).map e = G.map e ⊔ H.map e := by
  ext a b
  rw [SimpleGraph.map_adj e,sup_adj,SimpleGraph.map_adj e,SimpleGraph.map_adj e]
  constructor
  · rintro ⟨u,v,h | h,hu,hv⟩
    · exact Or.inl ⟨u,v,h,hu,hv⟩
    · exact Or.inr ⟨u,v,h,hu,hv⟩
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · exact ⟨u,v,Or.inl h,hu,hv⟩
    · exact ⟨u,v,Or.inr h,hu,hv⟩

namespace Identification

variable {P S : Shape} (p : Identification P S)

/-- Identify only the two vertices at the matrix multiplication boundary. -/
noncomputable def fresh (P S : Shape) : Identification P S :=
  ⟨fun j ↦ if j = S.left then some P.right else none,by simp,
    fun j k i hj hk ↦ by
      have hJ : j = S.left := by
        by_contra h
        change (if j = S.left then some P.right else none) = some i at hj
        rw [ite_eq_right h] at hj
        cases hj
      have hK : k = S.left := by
        by_contra h
        change (if k = S.left then some P.right else none) = some i at hk
        rw [ite_eq_right h] at hk
        cases hk
      exact hJ.trans hK.symm⟩

lemma fresh_shared_eq_singleton (P S : Shape) : (fresh P S).shared = {(fresh P S).old P.right} := by
  ext u
  rw [(fresh P S).mem_shared,mem_singleton]
  constructor
  · rintro ⟨⟨i,rfl⟩,j,he⟩
    have h := (fresh P S).overlap_iff.mp he
    change (if j = S.left then some P.right else none) = some i at h
    split_ifs at h with h'
    exact congrArg (fresh P S).old (Option.some.inj h).symm
  · rintro rfl
    exact ⟨⟨P.right,rfl⟩,⟨S.left,(fresh P S).join⟩⟩

lemma eq_fresh_of_card_shared_le_one (h : p.shared.card ≤ 1) : p = fresh P S := by
  have hShared : ({p.old P.right} : Finset p.Vertex) = p.shared :=
    eq_of_subset_of_card_le (singleton_subset_iff.mpr p.join_mem_shared) (by simpa only [card_singleton] using h)
  apply Subtype.ext
  funext j
  by_cases hJ : j = S.left
  · subst j
    exact p.property.1.trans (ite_eq_left rfl).symm
  · change p.val j = (if j = S.left then some P.right else none)
    rw [ite_eq_right hJ]
    cases he : p.val j with
    | none => rfl
    | some i =>
      have hMem : p.new j ∈ p.shared :=
        p.mem_shared.mpr ⟨⟨i,(p.new_of_some he).symm⟩,⟨j,rfl⟩⟩
      rw [← hShared,mem_singleton,← p.join] at hMem
      exact (hJ (p.new.injective hMem)).elim

lemma old_new_disjoint_of_card_shared_le_one (h : p.shared.card ≤ 1)
    {a b : p.Vertex} (hA : p.oldGraph.Adj a b) : ¬p.newGraph.Adj a b := by
  intro hB
  have ha : a ∈ p.shared := p.mem_shared.mpr ⟨p.mem_old_of_oldAdj hA,p.mem_new_of_newAdj hB⟩
  have hb : b ∈ p.shared := p.mem_shared.mpr ⟨p.mem_old_of_oldAdj hA.symm,p.mem_new_of_newAdj hB.symm⟩
  have hSub : ({a,b} : Finset p.Vertex) ⊆ p.shared := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  have hCard := card_le_card hSub
  rw [card_pair hA.ne] at hCard
  omega

lemma remaining_eq_sup_of_disjoint (h : ∀ {a b}, p.oldGraph.Adj a b → ¬p.newGraph.Adj a b) :
    p.remaining = p.oldGraph ⊔ p.newGraph := by
  ext a b
  constructor
  · rintro (⟨hA,_⟩ | ⟨hB,_⟩)
    · exact Or.inl hA
    · exact Or.inr hB
  · rintro (hA | hB)
    · exact Or.inl ⟨hA,h hA⟩
    · exact Or.inr ⟨hB,fun hA ↦ h hA hB⟩

lemma disjoint_of_no_newCancels (h : ¬∃ u, Incident p.newCancels u)
    {a b : p.Vertex} (hA : p.oldGraph.Adj a b) : ¬p.newGraph.Adj a b := by
  intro hB
  obtain ⟨u,v,hv,rfl,rfl⟩ := (SimpleGraph.map_adj p.new S.graph _ _).mp hB
  exact h ⟨u,v,hv,hA⟩

lemma liveShared_eq_shared_of_disjoint (h : ∀ {a b}, p.oldGraph.Adj a b → ¬p.newGraph.Adj a b)
    (hS : ∀ a, Incident S.graph a) : p.liveShared = p.shared := by
  ext u
  rw [p.mem_liveShared]
  refine and_iff_left_of_imp ?_
  intro hu
  obtain ⟨i,rfl⟩ := (p.mem_shared.mp hu).2
  obtain ⟨j,hj⟩ := hS i
  refine Or.inl ⟨p.new j,?_⟩
  rw [p.remaining_eq_sup_of_disjoint h]
  exact Or.inr (SimpleGraph.map_adj_apply.mpr hj)

lemma reachable_of_disjoint (h : ∀ {a b}, p.oldGraph.Adj a b → ¬p.newGraph.Adj a b)
    (hP : P.graph.Reachable P.left P.right) (hS : S.graph.Preconnected) :
    p.remaining.Reachable p.outputLeft p.outputRight := by
  rw [p.remaining_eq_sup_of_disjoint h]
  have h₁ := hP.map (SimpleGraph.Embedding.map p.old P.graph).toHom
  have h₂ := (hS S.left S.right).map (SimpleGraph.Embedding.map p.new S.graph).toHom
  have h₂' : p.newGraph.Reachable (p.new S.left) p.outputRight := h₂
  rw [p.join] at h₂'
  exact (h₁.mono le_sup_left).trans (h₂'.mono le_sup_right)

end Identification

namespace ChainTerm

variable (P : ChainTerm) (T : BasicShape)

/-- The appended block in the new shape, starting from its original cycle coordinates. -/
def appendedBlockEmb : Fin T.toShape.vertexCount ↪ Fin (P.append T).toShape.vertexCount :=
  (Equiv.neg (Fin (T.span+1))).toEmbedding.trans (P.tailEmb T)

lemma appendedBlockEmb_left :
    P.appendedBlockEmb T T.toShape.left = P.prefixEmb T P.toShape.right := by
  apply Fin.ext
  change P.span + (-(0 : Fin (T.span+1))).val = 0+P.span
  simp

lemma appendedBlockEmb_right :
    P.appendedBlockEmb T T.toShape.right = (P.append T).toShape.right := by
  apply Fin.ext
  change P.span + (-(1 : Fin (T.span+1))).val = (P.append T).span
  rw [← Fin.neg_last,neg_neg,span_append]
  rfl

lemma overlap_appendedBlock {i : Fin P.toShape.vertexCount} {j : Fin T.toShape.vertexCount}
    (he : P.prefixEmb T i = P.appendedBlockEmb T j) : j = T.toShape.left := by
  change Fin (T.span+1) at j
  have h := congrArg Fin.val he
  change 0+i.val = P.span+(- (j : Fin (T.span+1))).val at h
  have h₁ := i.isLt
  have hVal : (-(j : Fin (T.span+1))).val = 0 := by change i.val < P.span+1 at h₁; omega
  have hEq : -(j : Fin (T.span+1)) = (0 : Fin (T.span+1)) := Fin.ext hVal
  change (j : Fin (T.span+1)) = (0 : Fin (T.span+1))
  exact neg_eq_zero.mp hEq

private noncomputable def appendLabelings :
    Identification.Compatible P.toShape T.toShape (Fin (P.append T).toShape.vertexCount) :=
  ⟨(P.prefixEmb T,P.appendedBlockEmb T),(P.appendedBlockEmb_left T).symm⟩

private lemma appendLabelings_fresh :
    Identification.ofLabelings (P.appendLabelings T) = Identification.fresh P.toShape T.toShape := by
  apply Subtype.ext
  funext j
  by_cases hj : j = T.toShape.left
  · subst j
    change (Identification.ofLabelings (P.appendLabelings T)).val T.toShape.left =
      if T.toShape.left = T.toShape.left then some P.toShape.right else none
    rw [ite_eq_left rfl]
    exact (Identification.ofLabelings _).property.1
  · change _ = if j = T.toShape.left then some P.toShape.right else none
    rw [ite_eq_right hj]
    apply Identification.findOld_eq_none.mpr
    intro i hi
    exact hj (P.overlap_appendedBlock T hi)

/-- The unique gluing with just the common boundary is the appended shape. -/
theorem fresh_isomorphic_append :
    Nonempty ((Identification.fresh P.toShape T.toShape).shape.Isomorphism (P.append T).toShape) := by
  rw [← P.appendLabelings_fresh T]
  let fg := P.appendLabelings T
  let q := Identification.ofLabelings fg
  let e := Identification.quotientLabeling fg
  have hQ : q.shared.card = 1 := by
    change (Identification.ofLabelings (P.appendLabelings T)).shared.card = 1
    rw [P.appendLabelings_fresh T,Identification.fresh_shared_eq_singleton,card_singleton]
  have hC := q.card_vertex_add_shared
  rw [hQ] at hC
  have hCard : Fintype.card q.Vertex = Fintype.card (Fin (P.append T).toShape.vertexCount) := by
    rw [Fintype.card_fin,show (P.append T).toShape.vertexCount = (P.append T).span+1 from rfl,span_append]
    change Fintype.card q.Vertex+1 = (P.span+1)+(T.span+1) at hC
    omega
  let iso := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective,hCard⟩)
  have hOld (i : Fin P.toShape.vertexCount) : e (q.old i) = P.prefixEmb T i :=
    Identification.quotientLabeling_old fg i
  have hNew (i : Fin T.toShape.vertexCount) : e (q.new i) = P.appendedBlockEmb T i :=
    Identification.quotientLabeling_new fg i
  have hA : q.oldGraph.map e = P.graph.map (P.prefixEmb T) := by
    rw [Identification.oldGraph,SimpleGraph.map_map]
    exact congrArg (fun f ↦ P.graph.map f) (funext hOld)
  have hB : q.newGraph.map e = T.pathGraph.map (P.tailEmb T) := by
    rw [Identification.newGraph,SimpleGraph.map_map]
    have hEq : T.graph.map (e ∘ q.new) = T.graph.map (P.appendedBlockEmb T) :=
      congrArg (fun f ↦ T.graph.map f) (funext hNew)
    change T.graph.map (e ∘ q.new) = _
    rw [hEq]
    change T.graph.map ((P.tailEmb T) ∘ (Equiv.neg (Fin (T.span+1))).toEmbedding) = _
    rw [← SimpleGraph.map_map]
    congr 1
    exact (SimpleGraph.comap_symm T.graph (Equiv.neg (Fin (T.span+1)))).symm
  have hG : q.remaining.map e = (P.append T).graph := by
    rw [q.remaining_eq_sup_of_disjoint
      (fun h ↦ q.old_new_disjoint_of_card_shared_le_one hQ.le h),map_sup_embedding e,hA,hB,P.graph_append T]
  have hIso {a b : q.Vertex} :
      (P.append T).graph.Adj (e a) (e b) ↔ q.remaining.Adj a b := by
    rw [← hG]
    exact SimpleGraph.map_adj_apply
  refine ⟨⟨⟨q.numbering.symm.trans iso,?_⟩,?_,?_⟩⟩
  · intro a b
    change (P.append T).graph.Adj (e (q.numbering.symm a)) (e (q.numbering.symm b)) ↔ q.shape.graph.Adj a b
    rw [hIso]
    have hh := q.numbered_adj (u := q.numbering.symm a) (v := q.numbering.symm b)
    rw [q.numbering.apply_symm_apply,q.numbering.apply_symm_apply] at hh
    exact hh.symm
  · change e (q.numbering.symm q.shape.left) = _
    rw [← q.numbered_left,q.numbering.symm_apply_apply]
    apply (hOld _).trans
    exact Fin.ext rfl
  · change e (q.numbering.symm q.shape.right) = _
    rw [← q.numbered_right,q.numbering.symm_apply_apply]
    exact (hNew _).trans (P.appendedBlockEmb_right T)

end ChainTerm

end LovaszTheta.Independent
