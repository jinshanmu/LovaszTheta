module

public import LovaszTheta.TracePrefix

/-!
# Recovery of the return orientation and the next trace state

A common code fixes the waiting pair and identifies the two
possible return destinations. The prefix induction recovers all
exposed names, pairings, and boundary changes.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ} {c d : TraceBlocks V (l+2)}

private lemma eq_of_priorName_eq_of_named {k : ℕ} {u w : V}
    (he : priorName c v k u = priorName c v k w) (hn : priorName c v k w ≠ none) : u = w := by
  cases hw : priorName c v k w with
  | none => exact (hn hw).elim
  | some _ => exact eq_of_priorName_eq_some (he.trans hw) hw

private lemma PrefixAgreement.boundaryMatch {k : ℕ} {p : Fin (l+2)} (he : PrefixAgreement c d v k)
    (hp : p.val < k) {u w : V} (hn : priorName c v k u = priorName d v k w) :
    (u = (c.block p).left ↔ w = (d.block p).left) ∧
      (u = (c.block p).right ↔ w = (d.block p).right) := by
  have hEq := he.boundaryName hp
  constructor
  · constructor
    · intro hE
      apply eq_of_priorName_eq_of_named (v := v) (k := k)
        (hn.symm.trans ((congrArg (priorName c v k) hE).trans hEq.1))
      exact priorName_ne_none_of_exposed hp (exposedLabel_left d p)
    · intro hE
      apply eq_of_priorName_eq_of_named (v := v) (k := k)
        (hn.trans ((congrArg (priorName d v k) hE).trans hEq.1.symm))
      exact priorName_ne_none_of_exposed hp (exposedLabel_left c p)
  · constructor
    · intro hE
      apply eq_of_priorName_eq_of_named (v := v) (k := k)
        (hn.symm.trans ((congrArg (priorName c v k) hE).trans hEq.2))
      exact priorName_ne_none_of_exposed hp (exposedLabel_right d p)
    · intro hE
      apply eq_of_priorName_eq_of_named (v := v) (k := k)
        (hn.trans ((congrArg (priorName d v k) hE).trans hEq.2.symm))
      exact priorName_ne_none_of_exposed hp (exposedLabel_right c p)

private lemma PrefixAgreement.same_return_pair {i j : Fin (l+2)}
    (he : PrefixAgreement c d v j.val) (hD : d.RepeatedEdges) (hp : c.privatePair i j) :
    d.privatePair i j := by
  obtain ⟨p,hpD⟩ := (privateReturnAt_iff d j).mp (he.nextReturn.mp ((privateReturnAt_iff c j).mpr ⟨i,hp⟩))
  have hi : i ∈ c.waitingStarts j.val := mem_waitingStarts_iff.mpr ⟨hp.1.1,j,hp,le_rfl⟩
  rw [he.waiting] at hi
  obtain ⟨hi,q,hq,hJQ⟩ := mem_waitingStarts_iff.mp hi
  have hM := he.boundaryMatch hi he.incomingName
  have hEp := (return_left_is_endpoint hp).imp hM.1.mp hM.2.mp
  have hPair := waitingPair_unique_of_return_left hD hpD ⟨hq,hi,hJQ⟩ hEp
  rw [hPair.2] at hq
  exact hq

private lemma PrefixAgreement.otherEndpointName {i j : Fin (l+2)}
    (he : PrefixAgreement c d v j.val) (h : c.privatePair i j) :
    priorName c v j.val (otherEndpoint (c.block i) (c.block j).left) =
      priorName d v j.val (otherEndpoint (d.block i) (d.block j).left) := by
  have hEp := (he.boundaryMatch (p := i) h.1.1 he.incomingName).1
  have hn := he.boundaryName (i := i) h.1.1
  unfold otherEndpoint
  by_cases hL : (c.block j).left = (c.block i).left
  · rw [ite_eq_left hL,ite_eq_left (hEp.mp hL)]
    exact hn.2
  · rw [ite_eq_right hL,ite_eq_right (fun hh ↦ hL (hEp.mpr hh))]
    exact hn.1

private lemma PrefixAgreement.otherWaiting_forward {i j : Fin (l+2)} (he : PrefixAgreement c d v j.val)
    (hC : c.RepeatedEdges) (hc : c.privatePair i j) :
    c.otherWaiting i j → d.otherWaiting i j := by
  rintro ⟨p,q,hpq,hne,hm⟩
  have hp : p ∈ c.waitingStarts j.val := mem_waitingStarts_iff.mpr ⟨hpq.2.1,q,hpq.1,hpq.2.2⟩
  rw [he.waiting] at hp
  obtain ⟨hp,q',hq',hq⟩ := mem_waitingStarts_iff.mp hp
  have hEnd := endpoint_of_other_waiting hC hc hpq hne (otherEndpoint_mem_vertices _ _) hm
  have hM := he.boundaryMatch hp (he.otherEndpointName hc)
  refine ⟨p,q',⟨hq',hp,hq⟩,hne,?_⟩
  rcases hEnd.imp hM.1.mp hM.2.mp with hl | hr
  · rw [hl]
    exact (d.block p).left_mem_vertices
  · rw [hr]
    exact (d.block p).right_mem_vertices

private lemma not_nextReturn_of_not_otherWaiting (h : c.RepeatedEdges) {i j : Fin (l+2)}
    (hp : c.privatePair i j) (hn : ¬c.otherWaiting i j) :
    ¬privateReturnAt c (j.val+1) := by
  rintro ⟨p,q,hq,hPair⟩
  exact no_next_privateReturn_of_no_waiting_other h hp hq
    (fun a b hab hne hmem ↦ hn ⟨a,b,hab,hne,hmem⟩) ⟨p,hPair⟩

/-- A return in each trace has the same partner, starting side, and choice of destination. -/
structure ReturnAgreement (c d : TraceBlocks V (l+2)) (i j : Fin (l+2)) : Prop where
  paired : d.privatePair i j
  left : (c.block j).left = (c.block i).left ↔ (d.block j).left = (d.block i).left
  right : (c.block j).right = otherEndpoint (c.block i) (c.block j).left ↔
    (d.block j).right = otherEndpoint (d.block i) (d.block j).left

private lemma PrefixAgreement.return_agreement_aux {i j : Fin (l+2)}
    (he : PrefixAgreement c d v j.val) (hC : c.RepeatedEdges) (hD : d.RepeatedEdges)
    (h : encodeStep c v j = encodeStep d v j) (hp : c.privatePair i j) :
    ReturnAgreement c d i j ∧ (privateReturnAt c (j.val+1) ↔ privateReturnAt d (j.val+1)) := by
  have hP := he.same_return_pair hD hp
  have heL := (he.boundaryMatch (p := i) hp.1.1 he.incomingName).1
  have hOther : c.otherWaiting i j ↔ d.otherWaiting i j :=
    ⟨he.otherWaiting_forward hC hp,he.symm.otherWaiting_forward hD hP⟩
  have hb := congrArg StepCode.bit h
  simp only [encodeStep,stepBit_eq_of_return hp,stepBit_eq_of_return hP] at hb
  by_cases ht : c.otherWaiting i j
  · have ht' := hOther.mp ht
    have hForced (b : TraceBlocks V (l+2)) (hB : b.RepeatedEdges) (hP : b.privatePair i j)
        (hT : b.otherWaiting i j) :
        (b.block j).right = otherEndpoint (b.block i) (b.block j).left := by
      obtain ⟨p,q,hpq,hne,hmem⟩ := hT
      exact return_right_eq_otherEndpoint_of_waiting hB hP hpq hne hmem
    rw [ite_eq_left ht,ite_eq_left ht'] at hb
    exact ⟨⟨hP,heL,iff_of_true (hForced c hC hp ht) (hForced d hD hP ht')⟩,iff_of_equal_bits hb⟩
  · have ht' := fun h' ↦ ht (hOther.mpr h')
    rw [ite_eq_right ht,ite_eq_right ht'] at hb
    have hh := iff_of_equal_bits hb
    exact ⟨⟨hP,heL,not_iff_not.mp hh⟩,
      iff_of_false (not_nextReturn_of_not_otherWaiting hC hp ht)
        (not_nextReturn_of_not_otherWaiting hD hP ht')⟩

lemma PrefixAgreement.succ_return {i j : Fin (l+2)} (he : PrefixAgreement c d v j.val)
    (hC : c.RepeatedEdges) (hD : d.RepeatedEdges) (h : encodeStep c v j = encodeStep d v j)
    (hp : c.privatePair i j) : PrefixAgreement c d v (j.val+1) := by
  obtain ⟨hr,hNext⟩ := he.return_agreement_aux hC hD h hp
  have hn : priorName c v j.val (c.block j).right = priorName d v j.val (d.block j).right := by
    by_cases hc : (c.block j).right = otherEndpoint (c.block i) (c.block j).left
    · rw [hc,hr.right.mp hc]
      exact he.otherEndpointName hp
    · exact (priorName_private_destination hC hp hc v).trans
        (priorName_private_destination hD hr.paired (fun hd ↦ hc (hr.right.mpr hd)) v).symm
  refine he.extend (knownSlot_succ_eq_of_unmarked (notMem_markedPositions_of_privatePair hC hp).2
    (notMem_markedPositions_of_privatePair hD hr.paired).2 he.incomingName hn) ?_ hNext
  rw [waitingStarts_succ_return hC hp,waitingStarts_succ_return hD hr.paired,he.waiting]

/-- All exposed prefixes are determined by the code. -/
theorem prefixAgreement_of_code_eq (hC : c.RepeatedEdges) (hD : d.RepeatedEdges)
    (h : ∀ i, encodeStep c v i = encodeStep d v i) (k : ℕ) (hk : k ≤ l+2) :
    PrefixAgreement c d v k := by
  induction k with
  | zero => exact prefixAgreement_zero _ _ _
  | succ k ih =>
    let i : Fin (l+2) := ⟨k,by omega⟩
    have he := ih (by omega)
    by_cases hMark : i ∈ c.markedPositions
    · exact he.succ_marked hC hD (h i) hMark
    · by_cases hRet : privateReturnAt c i.val
      · obtain ⟨p,hp⟩ := (privateReturnAt_iff c i).mp hRet
        exact he.succ_return hC hD (h i) hp
      · exact he.succ_forward hC hD (h i) hMark hRet

/-- A code recovers every pair and every change of boundaries. -/
theorem returnAgreement_of_code_eq (hC : c.RepeatedEdges) (hD : d.RepeatedEdges)
    (h : ∀ i, encodeStep c v i = encodeStep d v i) {i j : Fin (l+2)} (hp : c.privatePair i j) :
    ReturnAgreement c d i j :=
  ((prefixAgreement_of_code_eq hC hD h j.val j.isLt.le).return_agreement_aux hC hD (h j) hp).1

end TraceBlocks

end LovaszTheta.Independent
