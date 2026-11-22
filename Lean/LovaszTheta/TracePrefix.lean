module

public import LovaszTheta.TraceStepCode

/-!
# Agreement of exposed trace prefixes

Two traces with the same code have the same marked shapes.
At a marked or forward step their exposed names and their
waiting state evolve in the same way.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ} {c d : TraceBlocks V (l+2)}

lemma iff_of_equal_bits {P Q : Prop} [Decidable P] [Decidable Q] (h : decide P = decide Q) : P ↔ Q := by
  by_cases hp : P <;> by_cases hq : Q
  all_goals simp [hp,hq] at h ⊢

/-- The information in the trace state before the next step. -/
structure PrefixAgreement (c d : TraceBlocks V (l+2)) (v k : ℕ) : Prop where
  names : ∀ s : Name l v, knownSlot c v k s = knownSlot d v k s
  waiting : c.waitingStarts k = d.waitingStarts k
  nextReturn : privateReturnAt c k ↔ privateReturnAt d k

lemma PrefixAgreement.symm {k : ℕ} (he : PrefixAgreement c d v k) : PrefixAgreement d c v k :=
  ⟨fun s ↦ (he.names s).symm,he.waiting.symm,he.nextReturn.symm⟩

lemma prefixAgreement_zero (c d : TraceBlocks V (l+2)) (v : ℕ) : PrefixAgreement c d v 0 :=
  ⟨fun s ↦ (knownSlot_zero c s).trans (knownSlot_zero d s).symm,
    (waitingStarts_zero c).trans (waitingStarts_zero d).symm,
    iff_of_false (not_privateReturnAt_zero c) (not_privateReturnAt_zero d)⟩

lemma PrefixAgreement.boundaryName {k : ℕ} (he : PrefixAgreement c d v k) {i : Fin (l+2)}
    (hi : i.val < k) :
    priorName c v k (c.block i).left = priorName d v k (d.block i).left ∧
      priorName c v k (c.block i).right = priorName d v k (d.block i).right := by
  constructor
  · have h := he.names (slot i 0)
    rwa [knownSlot_eq_priorName hi (exposedLabel_left c i),knownSlot_eq_priorName hi (exposedLabel_left d i)] at h
  · have h := he.names (slot i 1)
    rwa [knownSlot_eq_priorName hi (exposedLabel_right c i),knownSlot_eq_priorName hi (exposedLabel_right d i)] at h

lemma PrefixAgreement.incomingName {i : Fin (l+2)} (he : PrefixAgreement c d v i.val) :
    priorName c v i.val (c.block i).left = priorName d v i.val (d.block i).left := by
  by_cases hi : 0 < i.val
  · obtain ⟨p,hp,hc⟩ := c.exists_predecessor_stitch hi
    obtain ⟨q,hq,hd⟩ := d.exists_predecessor_stitch hi
    have hpq : p = q := Fin.ext (by omega)
    subst q
    have heq := (he.boundaryName (i := p) (by omega)).2
    rwa [hc,hd] at heq
  · have h₀ : i.val = 0 := by omega
    have hNone (b : TraceBlocks V (l+2)) : ¬b.Earlier i (b.block i).left := by
      rintro ⟨j,hj,_⟩
      have h : j.val < i.val := hj
      omega
    rw [priorName_none_of_no_earlier (hNone c),priorName_none_of_no_earlier (hNone d)]

lemma PrefixAgreement.extend {i : Fin (l+2)} (he : PrefixAgreement c d v i.val)
    (hNames : ∀ p : Fin (v+2), knownSlot c v (i.val+1) (slot i p) = knownSlot d v (i.val+1) (slot i p))
    (hWait : c.waitingStarts (i.val+1) = d.waitingStarts (i.val+1))
    (hType : privateReturnAt c (i.val+1) ↔ privateReturnAt d (i.val+1)) :
    PrefixAgreement c d v (i.val+1) := by
  refine ⟨fun s ↦ ?_,hWait,hType⟩
  rcases lt_trichotomy (coordinates s).1 i with hlt | hEq | hgt
  · rw [knownSlot_persist (c := c) (Nat.le_succ _) hlt,knownSlot_persist (c := d) (Nat.le_succ _) hlt]
    exact he.names s
  · have hs : slot i (coordinates s).2 = s :=
      (congrArg (fun j ↦ slot j (coordinates s).2) hEq.symm).trans (slot_coordinates s)
    exact hs ▸ hNames (coordinates s).2
  · have hn : ¬(coordinates s).1.val < i.val+1 := not_lt_of_ge hgt
    rw [knownSlot_of_not_lt hn,knownSlot_of_not_lt hn]

lemma mem_marked_iff_of_stepCode_eq {i : Fin (l+2)} (h : encodeStep c v i = encodeStep d v i) :
    i ∈ c.markedPositions ↔ i ∈ d.markedPositions := by
  have hE := congrArg StepCode.markedShape h
  simp only [encodeStep] at hE
  by_cases hc : i ∈ c.markedPositions <;> by_cases hd : i ∈ d.markedPositions
  all_goals simp [hc,hd] at hE ⊢

private lemma knownSlot_succ_eq_of_mark {i : Fin (l+2)}
    (h : encodeStep c v i = encodeStep d v i) (hc : i ∈ c.markedPositions) (p : Fin (v+2)) :
    knownSlot c v (i.val+1) (slot i p) = knownSlot d v (i.val+1) (slot i p) := by
  have hd := (mem_marked_iff_of_stepCode_eq h).mp hc
  have hs := congrArg StepCode.markedShape h
  simp only [encodeStep,ite_eq_left hc,ite_eq_left hd,Option.some.injEq] at hs
  have hSize := congrArg BasicShape.additionalVertices hs
  have href := congrFun (congrArg StepCode.reference h) p
  rw [knownSlot_succ_current,knownSlot_succ_current]
  simp only [exposedLabel,ite_eq_left hc,ite_eq_left hd]
  by_cases hp : p.val < (c.block i).shape.additionalVertices+2
  · have hp' : p.val < (d.block i).shape.additionalVertices+2 := hSize ▸ hp
    simp only [encodeStep,ite_eq_left hc,ite_eq_left hd,exposedLabel,dite_eq_left hp,dite_eq_left hp',Option.bind_some] at href
    simp only [dite_eq_left hp,dite_eq_left hp',Option.map_some,href]
  · have hp' : ¬p.val < (d.block i).shape.additionalVertices+2 := hSize ▸ hp
    simp only [dite_eq_right hp,dite_eq_right hp',Option.map_none]

lemma knownSlot_succ_eq_of_unmarked {i : Fin (l+2)}
    (hc : i ∉ c.markedPositions) (hd : i ∉ d.markedPositions)
    (hL : priorName c v i.val (c.block i).left = priorName d v i.val (d.block i).left)
    (hR : priorName c v i.val (c.block i).right = priorName d v i.val (d.block i).right)
    (p : Fin (v+2)) :
    knownSlot c v (i.val+1) (slot i p) = knownSlot d v (i.val+1) (slot i p) := by
  rw [knownSlot_succ_current,knownSlot_succ_current]
  simp only [exposedLabel,ite_eq_right hc,ite_eq_right hd]
  by_cases hp : p = 0
  · simp only [ite_eq_left hp,Option.map_some,hL]
  · simp only [ite_eq_right hp]
    by_cases hp' : p = 1
    · simp only [ite_eq_left hp',Option.map_some,hR]
    · simp only [ite_eq_right hp',Option.map_none]

lemma PrefixAgreement.succ_marked {i : Fin (l+2)} (he : PrefixAgreement c d v i.val)
    (hC : c.RepeatedEdges) (hD : d.RepeatedEdges) (h : encodeStep c v i = encodeStep d v i)
    (hc : i ∈ c.markedPositions) : PrefixAgreement c d v (i.val+1) := by
  have hd := (mem_marked_iff_of_stepCode_eq h).mp hc
  have hcRet : ¬privateReturnAt c i.val := fun hr ↦ by
    obtain ⟨j,hp⟩ := (privateReturnAt_iff c i).mp hr
    exact (notMem_markedPositions_of_privatePair hC hp).2 hc
  have hdRet : ¬privateReturnAt d i.val := fun hr ↦ hcRet (he.nextReturn.mpr hr)
  refine he.extend (knownSlot_succ_eq_of_mark h hc) ?_ ?_
  · rw [waitingStarts_succ_marked hC hc,waitingStarts_succ_marked hD hd,he.waiting]
  · have hb := congrArg StepCode.bit h
    simp only [encodeStep,stepBit_eq_nextType_of_no_return hcRet,stepBit_eq_nextType_of_no_return hdRet] at hb
    exact iff_of_equal_bits hb

lemma PrefixAgreement.succ_forward {i : Fin (l+2)} (he : PrefixAgreement c d v i.val)
    (hC : c.RepeatedEdges) (hD : d.RepeatedEdges) (h : encodeStep c v i = encodeStep d v i)
    (hc : i ∉ c.markedPositions) (hcRet : ¬privateReturnAt c i.val) : PrefixAgreement c d v (i.val+1) := by
  have hd := fun hm ↦ hc ((mem_marked_iff_of_stepCode_eq h).mpr hm)
  have hdRet : ¬privateReturnAt d i.val := fun hr ↦ hcRet (he.nextReturn.mpr hr)
  obtain ⟨j,hcj | hcj⟩ := exists_privatePair_of_notMem_marked hc
  swap
  · exact (hcRet ((privateReturnAt_iff c i).mpr ⟨j,hcj⟩)).elim
  obtain ⟨k,hdk | hdk⟩ := exists_privatePair_of_notMem_marked hd
  swap
  · exact (hdRet ((privateReturnAt_iff d i).mpr ⟨k,hdk⟩)).elim
  refine he.extend (knownSlot_succ_eq_of_unmarked hc hd he.incomingName
    ((priorName_forward_right hC hcj v).trans (priorName_forward_right hD hdk v).symm)) ?_ ?_
  · rw [waitingStarts_succ_forward hC hcj,waitingStarts_succ_forward hD hdk,he.waiting]
  · have hb := congrArg StepCode.bit h
    simp only [encodeStep,stepBit_eq_nextType_of_no_return hcRet,stepBit_eq_nextType_of_no_return hdRet] at hb
    exact iff_of_equal_bits hb

end TraceBlocks

end LovaszTheta.Independent
