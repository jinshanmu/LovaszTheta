module

public import LovaszTheta.TraceRecovery

/-!
# Equality-pattern recovery

The shared code fixes the return orientation. With the forward
shapes given, transporting the roles of each return back to its
forward block recovers every equality of labels.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l v : ℕ} {c d : TraceBlocks V (l+2)}

lemma ReturnAgreement.boundaryChange_eq {i j : Fin (l+2)} (he : ReturnAgreement c d i j) :
    (c.block i).boundaryChange (c.block j) = (d.block i).boundaryChange (d.block j) := by
  unfold LabeledBlock.boundaryChange
  congr 1
  · simp only [he.left]
  · simp only [he.right]

private lemma frame_values_eq {a : BoundaryChange} {n m : ℕ} (h : n = m)
    {u : Fin (n+2)} {w : Fin (m+2)} (he : u.val = w.val) :
    (a.frame n u).val = (a.frame m w).val := by
  subst m
  rw [Fin.ext he]

private lemma paired_vals_eq {i j : Fin (l+2)} (hC : c.privatePair i j) (hE : ReturnAgreement c d i j)
    (he : (c.block i).shape = (d.block i).shape)
    {u : Fin ((c.block i).shape.additionalVertices+2)} {w : Fin ((d.block i).shape.additionalVertices+2)}
    (hVals : u.val = w.val) :
    ((c.block i).pairedCyclePermutation (c.block j) hC.1.2.2.2.1 u).val =
      ((d.block i).pairedCyclePermutation (d.block j) hE.paired.1.2.2.2.1 w).val := by
  rw [LabeledBlock.pairedCyclePermutation_eq_change _ _ _ (return_left_is_endpoint hC),
    LabeledBlock.pairedCyclePermutation_eq_change _ _ _ (return_left_is_endpoint hE.paired),
    hE.boundaryChange_eq]
  exact frame_values_eq (congrArg BasicShape.additionalVertices he) hVals

private lemma forwardRight_iff {i j : Fin (l+2)} (hC : c.privatePair i j) (hE : ReturnAgreement c d i j)
    (he : (c.block i).shape = (d.block i).shape)
    {p : Fin (v+2)} {u w : V} (hu : fullLabel c i p = some u) (hw : fullLabel d i p = some w) :
    u = (c.block j).right ↔ w = (d.block j).right := by
  obtain ⟨a,ha,haLabel⟩ := fullLabel_eq_some_iff.mp hu
  obtain ⟨b,hb,hbLabel⟩ := fullLabel_eq_some_iff.mp hw
  have hA := LabeledBlock.label_pairedCyclePermutation_right (c.block i) (c.block j) hC.1.2.2.2.1
  have hB := LabeledBlock.label_pairedCyclePermutation_right (d.block i) (d.block j) hE.paired.1.2.2.2.1
  rw [← haLabel,← hbLabel,← hA,← hB,(c.block i).label.injective.eq_iff,(d.block i).label.injective.eq_iff]
  rw [Fin.ext_iff,Fin.ext_iff,ha,hb,paired_vals_eq hC hE he (by simp : (1 : Fin ((c.block i).shape.additionalVertices+2)).val =
    (1 : Fin ((d.block i).shape.additionalVertices+2)).val)]

private lemma sharedTag_of_forward {i j : Fin (l+2)} (hc : c.RepeatedEdges) (hd : d.RepeatedEdges)
    (hCode : ∀ i, encodeStep c v i = encodeStep d v i)
    (hFin : PrefixAgreement c d v (l+2)) (hp : c.privatePair i j) (he : (c.block i).shape = (d.block i).shape)
    {p : Fin (v+2)} {u w : V} (hu : fullLabel c i p = some u) (hw : fullLabel d i p = some w) :
    ∃ tag, LabelRepresentation c v u tag ∧ LabelRepresentation d v w tag := by
  have hRet := returnAgreement_of_code_eq hc hd hCode hp
  have hLeft (b : TraceBlocks V (l+2)) : fullLabel (v := v) b i 0 = some (b.block i).left :=
    fullLabel_eq_some_iff.mpr ⟨0,rfl,rfl⟩
  have hRight (b : TraceBlocks V (l+2)) : fullLabel (v := v) b i 1 = some (b.block i).right :=
    fullLabel_eq_some_iff.mpr ⟨1,by simp,rfl⟩
  by_cases h₀ : p = 0
  · subst p
    have hU := Option.some.inj (hu.symm.trans (hLeft c))
    have hW := Option.some.inj (hw.symm.trans (hLeft d))
    exact exists_shared_representation_of_exposed hFin (hU.symm ▸ exposedLabel_left c i)
      (hW.symm ▸ exposedLabel_left d i)
  by_cases h₁ : p = 1
  · subst p
    have hU := Option.some.inj (hu.symm.trans (hRight c))
    have hW := Option.some.inj (hw.symm.trans (hRight d))
    exact exists_shared_representation_of_exposed hFin (hU.symm ▸ exposedLabel_right c i)
      (hW.symm ▸ exposedLabel_right d i)
  · have hDest := forwardRight_iff hp hRet he hu hw
    by_cases hE : u = (c.block j).right
    · exact exists_shared_representation_of_exposed hFin
        (hE.symm ▸ exposedLabel_right c j) ((hDest.mp hE).symm ▸ exposedLabel_right d j)
    · refine ⟨Sum.inr (slot i p),?_,?_⟩
      · exact internal_label_is_private hc hp hu
          (fun hEq ↦ h₀ (fullLabel_roles_unique hu (hEq.symm ▸ hLeft c)))
          (fun hEq ↦ h₁ (fullLabel_roles_unique hu (hEq.symm ▸ hRight c))) hE
      · exact internal_label_is_private hd hRet.paired hw
          (fun hEq ↦ h₀ (fullLabel_roles_unique hw (hEq.symm ▸ hLeft d)))
          (fun hEq ↦ h₁ (fullLabel_roles_unique hw (hEq.symm ▸ hRight d))) (fun hEq ↦ hE (hDest.mpr hEq))

private lemma sharedTag_of_return {i j : Fin (l+2)} (hc : c.RepeatedEdges) (hd : d.RepeatedEdges)
    (hCode : ∀ i, encodeStep c v i = encodeStep d v i)
    (hFin : PrefixAgreement c d v (l+2)) (hp : c.privatePair i j) (he : (c.block i).shape = (d.block i).shape)
    (hSize : (c.block i).shape.additionalVertices ≤ v)
    {p : Fin (v+2)} {u w : V} (hu : fullLabel c j p = some u) (hw : fullLabel d j p = some w) :
    ∃ tag, LabelRepresentation c v u tag ∧ LabelRepresentation d v w tag := by
  obtain ⟨a,ha,haLabel⟩ := fullLabel_eq_some_iff.mp hu
  obtain ⟨b,hb,hbLabel⟩ := fullLabel_eq_some_iff.mp hw
  have hRet := returnAgreement_of_code_eq hc hd hCode hp
  let hC := hp.1.2.2.2.1
  let hD := hRet.paired.1.2.2.2.1
  let eC := finCongr (congrArg (·+2) (LabeledBlock.additionalVertices_eq_of_graph_eq hC))
  let eD := finCongr (congrArg (·+2) (LabeledBlock.additionalVertices_eq_of_graph_eq hD))
  let r := (c.block i).pairedCyclePermutation (c.block j) hC (eC.symm a)
  let s := (d.block i).pairedCyclePermutation (d.block j) hD (eD.symm b)
  have hRC : (c.block i).label r = u := by
    unfold r
    rw [LabeledBlock.label_pairedCyclePermutation_apply]
    exact (congrArg (c.block j).label (eC.apply_symm_apply a)).trans haLabel
  have hRD : (d.block i).label s = w := by
    unfold s
    rw [LabeledBlock.label_pairedCyclePermutation_apply]
    exact (congrArg (d.block j).label (eD.apply_symm_apply b)).trans hbLabel
  have hRS : r.val = s.val := paired_vals_eq hp hRet he (ha.trans hb.symm)
  let q : Fin (v+2) := ⟨r.val,r.isLt.trans_le (Nat.add_le_add_right hSize 2)⟩
  exact sharedTag_of_forward hc hd hCode hFin hp he (p := q)
    (fullLabel_eq_some_iff.mpr ⟨r,rfl,hRC⟩) (fullLabel_eq_some_iff.mpr ⟨s,hRS.symm,hRD⟩)

private lemma sharedTag_of_code_eq (hc : c.RepeatedEdges) (hd : d.RepeatedEdges)
    (hCode : ∀ i, encodeStep c v i = encodeStep d v i)
    (hF : ∀ i j, c.privatePair i j → (c.block i).shape = (d.block i).shape)
    (hSize : ∀ i, (c.block i).shape.additionalVertices ≤ v)
    {i : Fin (l+2)} {p : Fin (v+2)} {u w : V} (hu : fullLabel c i p = some u) (hw : fullLabel d i p = some w) :
    ∃ tag, LabelRepresentation c v u tag ∧ LabelRepresentation d v w tag := by
  have hFin := prefixAgreement_of_code_eq hc hd hCode (l+2) le_rfl
  by_cases hi : i ∈ c.markedPositions
  · have hi' := (mem_marked_iff_of_stepCode_eq (hCode i)).mp hi
    exact exists_shared_representation_of_exposed hFin
      (by rw [exposedLabel,ite_eq_left hi]; exact hu)
      (by rw [exposedLabel,ite_eq_left hi']; exact hw)
  · obtain ⟨j,h | h⟩ := exists_privatePair_of_notMem_marked hi
    · exact sharedTag_of_forward hc hd hCode hFin h (hF i j h) hu hw
    · exact sharedTag_of_return hc hd hCode hFin h (hF j i h) (hSize j) hu hw

/-- Equal codes and forward shapes recover all pairwise equalities of labels. -/
theorem labels_eq_iff_of_code_eq (hc : c.RepeatedEdges) (hd : d.RepeatedEdges)
    (hCode : ∀ i, encodeStep c v i = encodeStep d v i)
    (hF : ∀ i j, c.privatePair i j → (c.block i).shape = (d.block i).shape)
    (hSize : ∀ i, (c.block i).shape.additionalVertices ≤ v)
    {i j : Fin (l+2)} {p q : Fin (v+2)} {u w u' w' : V}
    (huc : fullLabel c i p = some u) (hud : fullLabel d i p = some u')
    (hwc : fullLabel c j q = some w) (hwd : fullLabel d j q = some w') :
    u = w ↔ u' = w' := by
  obtain ⟨a,ha,ha'⟩ := sharedTag_of_code_eq hc hd hCode hF hSize huc hud
  obtain ⟨b,hb,hb'⟩ := sharedTag_of_code_eq hc hd hCode hF hSize hwc hwd
  exact (label_eq_iff_tag_eq ha hb).trans (label_eq_iff_tag_eq ha' hb').symm

/-- Once the forward shapes are specified, the code determines the whole shape word. -/
theorem shape_eq_of_code_eq (hc : c.RepeatedEdges) (hd : d.RepeatedEdges)
    (hCode : ∀ i, encodeStep c v i = encodeStep d v i)
    (hF : ∀ i j, c.privatePair i j → (c.block i).shape = (d.block i).shape) (i : Fin (l+2)) :
    (c.block i).shape = (d.block i).shape := by
  by_cases hi : i ∈ c.markedPositions
  · have h := congrArg StepCode.markedShape (hCode i)
    have hd' := (mem_marked_iff_of_stepCode_eq (hCode i)).mp hi
    simpa only [encodeStep,ite_eq_left hi,ite_eq_left hd',Option.some.injEq] using h
  · obtain ⟨j,h | h⟩ := exists_privatePair_of_notMem_marked hi
    · exact hF i j h
    · have hr := returnAgreement_of_code_eq hc hd hCode h
      have he := LabeledBlock.inReturnFrame_of_graph_eq (c.block j) (c.block i) h.1.2.2.2.1 (return_left_is_endpoint h)
      have he' := LabeledBlock.inReturnFrame_of_graph_eq (d.block j) (d.block i) hr.paired.1.2.2.2.1
        (return_left_is_endpoint hr.paired)
      rw [← hr.boundaryChange_eq,← hF j i h] at he'
      exact InReturnFrame.right_unique he he'

end TraceBlocks

end LovaszTheta.Independent
