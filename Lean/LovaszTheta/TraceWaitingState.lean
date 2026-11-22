module

public import LovaszTheta.TraceExposure

/-!
# State transitions for the trace code

Waiting pairs are inserted at a forward step and removed at its
return. Old names detect the other waiting endpoint, which decides
whether the bit describes the destination or the next type.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l : ℕ} {c : TraceBlocks V (l+2)}

/-- Forward positions of pairs that have not yet returned at a prefix. -/
noncomputable def waitingStarts (c : TraceBlocks V (l+2)) (k : ℕ) : Finset (Fin (l+2)) :=
  univ.filter fun p ↦ p.val < k ∧ ∃ q, c.privatePair p q ∧ k ≤ q.val

lemma mem_waitingStarts_iff {k : ℕ} {p : Fin (l+2)} :
    p ∈ c.waitingStarts k ↔ p.val < k ∧ ∃ q, c.privatePair p q ∧ k ≤ q.val := by
  unfold waitingStarts
  rw [mem_filter]
  simp only [mem_univ,true_and]

lemma waitingStarts_zero (c : TraceBlocks V (l+2)) : c.waitingStarts 0 = ∅ := by
  ext i
  simp only [mem_waitingStarts_iff, Nat.not_lt_zero,false_and,notMem_empty]

private lemma mem_waitingStarts_succ_iff {i p : Fin (l+2)} :
    p ∈ c.waitingStarts (i.val+1) ↔
      (p ∈ c.waitingStarts i.val ∧ ¬c.privatePair p i) ∨
        (p = i ∧ ∃ q, c.privatePair i q) := by
  rw [mem_waitingStarts_iff,mem_waitingStarts_iff]
  constructor
  · rintro ⟨hp,q,hq,hQi⟩
    by_cases hP : p = i
    · exact Or.inr ⟨hP,q,hP ▸ hq⟩
    · have hp' : p.val < i.val := by
        have hNe : p.val ≠ i.val := fun he ↦ hP (Fin.ext he)
        omega
      refine Or.inl ⟨⟨hp',q,hq,by omega⟩,fun he ↦ ?_⟩
      have hEq := c.exactPair_right_unique he.1 hq.1
      have hEq' := congrArg Fin.val hEq
      omega
  · rintro (⟨⟨hp,q,hq,hqi⟩,hn⟩ | ⟨rfl,q,hq⟩)
    · refine ⟨by omega,q,hq,?_⟩
      have hEq : i ≠ q := fun he ↦ hn (he.symm ▸ hq)
      have hEq' : i.val ≠ q.val := fun he ↦ hEq (Fin.ext he)
      omega
    · exact ⟨Nat.lt_succ_self _,q,hq,hq.1.1⟩

theorem waitingStarts_succ_marked (h : c.RepeatedEdges) {i : Fin (l+2)} (hi : i ∈ c.markedPositions) :
    c.waitingStarts (i.val+1) = c.waitingStarts i.val := by
  ext p
  rw [mem_waitingStarts_succ_iff]
  constructor
  · rintro (⟨hp,_⟩ | ⟨rfl,q,hq⟩)
    · exact hp
    · exact ((notMem_markedPositions_of_privatePair h hq).1 hi).elim
  · exact fun hp ↦ Or.inl ⟨hp,fun hP ↦ (notMem_markedPositions_of_privatePair h hP).2 hi⟩

theorem waitingStarts_succ_forward (h : c.RepeatedEdges) {i j : Fin (l+2)} (hp : c.privatePair i j) :
    c.waitingStarts (i.val+1) = insert i (c.waitingStarts i.val) := by
  ext p
  rw [mem_waitingStarts_succ_iff,mem_insert]
  constructor
  · rintro (⟨hm,_⟩ | ⟨he,_⟩)
    · exact Or.inr hm
    · exact Or.inl he
  · rintro (he | hm)
    · exact Or.inr ⟨he,j,hp⟩
    · exact Or.inl ⟨hm,fun hRet ↦ not_forward_and_return h
        (forward_return_of_exactPair h hp.1).1 (forward_return_of_exactPair h hRet.1).2⟩

theorem waitingStarts_succ_return (h : c.RepeatedEdges) {i j : Fin (l+2)} (hp : c.privatePair i j) :
    c.waitingStarts (j.val+1) = (c.waitingStarts j.val).erase i := by
  ext p
  rw [mem_waitingStarts_succ_iff,mem_erase]
  constructor
  · rintro (⟨hm,hn⟩ | ⟨rfl,q,hq⟩)
    · exact ⟨fun he ↦ hn (he.symm ▸ hp),hm⟩
    · exact (not_forward_and_return h (forward_return_of_exactPair h hq.1).1
        (forward_return_of_exactPair h hp.1).2).elim
  · rintro ⟨hn,hm⟩
    exact Or.inl ⟨hm,fun hP ↦ hn (c.exactPair_left_unique hP.1 hp.1)⟩

lemma otherEndpoint_mem_vertices (b : LabeledBlock V) (u : V) : otherEndpoint b u ∈ b.vertices := by
  unfold otherEndpoint
  split_ifs
  · exact b.right_mem_vertices
  · exact b.left_mem_vertices

/-- A visible endpoint of one waiting pair can only be an endpoint of a second waiting pair. -/
theorem endpoint_of_other_waiting (h : c.RepeatedEdges)
    {i j p q : Fin (l+2)} (hp : c.privatePair i j) (hq : c.waitingPair j p q)
    (hne : p ≠ i) {u : V} (huI : u ∈ (c.block i).vertices) (huP : u ∈ (c.block p).vertices) :
    u = (c.block p).left ∨ u = (c.block p).right := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · by_contra! hn
    exact hq.1.2 u ⟨huP,hn.1,hn.2,i,hlt,hp.1.1.trans_le hq.2.2,huI⟩
  · exact Or.inl ((forward_return_of_exactPair h hq.1.1).1 u huP ⟨i,hgt,huI⟩)

/-- An unmarked forward step exposes a fresh right name. -/
theorem priorName_forward_right (h : c.RepeatedEdges) {i j : Fin (l+2)} (hp : c.privatePair i j) (v : ℕ) :
    priorName c v i.val (c.block i).right = none := by
  apply priorName_none_of_no_earlier
  exact fun he ↦ (c.block i).left_ne_right
    (((forward_return_of_exactPair h hp.1).1 _ (c.block i).right_mem_vertices he).symm)

/-- A private destination at the return receives its first exposed name there. -/
theorem priorName_private_destination (h : c.RepeatedEdges)
    {i j : Fin (l+2)} (hp : c.privatePair i j)
    (hDest : (c.block j).right ≠ otherEndpoint (c.block i) (c.block j).left) (v : ℕ) :
    priorName c v j.val (c.block j).right = none := by
  let u := (c.block j).right
  have hU : u ∈ (c.block i).vertices :=
    (LabeledBlock.vertices_eq_of_graph_eq hp.1.2.2.2.1).symm ▸ (c.block j).right_mem_vertices
  have hNe : u ≠ (c.block j).left := (c.block j).left_ne_right.symm
  have hP : u ≠ (c.block i).left ∧ u ≠ (c.block i).right := by
    rcases return_left_is_endpoint hp with hL | hR
    · refine ⟨fun e ↦ hNe (e.trans hL.symm),?_⟩
      simpa only [otherEndpoint,hL,ite_true] using hDest
    · refine ⟨?_,fun e ↦ hNe (e.trans hR.symm)⟩
      simpa only [otherEndpoint,hR,ite_eq_right (c.block i).left_ne_right.symm] using hDest
  apply (priorName_eq_none_iff _ _ _ _).mpr
  rintro ⟨s,hS⟩
  have he := mem_priorSlots.mp hS
  let k := (coordinates s).1
  have hKu : u ∈ (c.block k).vertices := mem_vertices_of_exposedLabel he.2
  rcases lt_trichotomy k i with hlt | heq | hgt
  · exact hP.1 ((forward_return_of_exactPair h hp.1).1 u hU ⟨k,hlt,hKu⟩)
  · have hExp := he.2
    change exposedLabel c k (coordinates s).2 = some u at hExp
    rw [heq,exposedLabel,ite_eq_right (notMem_markedPositions_of_privatePair h hp).1] at hExp
    split_ifs at hExp
    · exact hP.1 (Option.some.inj hExp).symm
    · exact hP.2 (Option.some.inj hExp).symm
  · exact hp.2 u ⟨hU,hP.1,hP.2,k,hgt,he.1,hKu⟩

end TraceBlocks

end LovaszTheta.Independent
