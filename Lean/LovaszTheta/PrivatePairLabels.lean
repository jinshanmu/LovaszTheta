module

public import LovaszTheta.UnpairedBlocks

/-!
# Private labels of the unmarked pairs

A pair's first intervening use of a private label belongs to an
unpaired block. Each such label was introduced by a unique
forward block, so the number of marked pairs is controlled by
the number of labels in the unpaired blocks.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent.TraceBlocks

variable {V : Type*} {l : ℕ} (c : TraceBlocks V (l+2))

lemma exactPair_shareEdge {i j : Fin (l+2)} (h : exactPair c.block i j) : ShareEdge c.block i j := by
  have he := (c.block i).graph_adj_left_right
  exact ⟨_,_,he,h.2.2.2.1 ▸ he⟩

lemma exactPair_right_unique {i j k : Fin (l+2)} (h : exactPair c.block i j) (h' : exactPair c.block i k) :
    j = k := by
  by_contra hne
  exact h.2.2.2.2 k h'.1.ne' (Ne.symm hne) (c.exactPair_shareEdge h')

lemma exactPair_left_unique {i j k : Fin (l+2)} (h : exactPair c.block i j) (h' : exactPair c.block k j) :
    i = k := by
  by_contra hne
  have he : (c.block i).graph = (c.block k).graph := h.2.2.2.1.trans h'.2.2.2.1.symm
  have hS : ShareEdge c.block i k := ⟨_,_,(c.block i).graph_adj_left_right,he ▸ (c.block i).graph_adj_left_right⟩
  exact h.2.2.2.2 k (Ne.symm hne) h'.1.ne hS

/-- An internal label of the forward block that occurs before its matched return. -/
def InterveningPrivateLabel (i j : Fin (l+2)) (u : V) : Prop :=
  u ∈ (c.block i).vertices ∧ u ≠ (c.block i).left ∧ u ≠ (c.block i).right ∧
    ∃ k, i < k ∧ k < j ∧ u ∈ (c.block k).vertices

/-- The exact pairs with a private label that is used before the return. -/
noncomputable def markedPairs : Finset (Fin (l+2) × Fin (l+2)) :=
  univ.filter fun p ↦ exactPair c.block p.1 p.2 ∧ ∃ u, c.InterveningPrivateLabel p.1 p.2 u

lemma mem_markedPairs {p : Fin (l+2) × Fin (l+2)} :
    p ∈ c.markedPairs ↔ exactPair c.block p.1 p.2 ∧ ∃ u, c.InterveningPrivateLabel p.1 p.2 u := by
  unfold markedPairs
  rw [Finset.mem_filter]
  simp only [mem_univ,true_and]

lemma exists_predecessor_stitch {k : Fin (l+2)} (hk : 0 < k.val) :
    ∃ p : Fin (l+2), p.val+1 = k.val ∧ (c.block p).right = (c.block k).left := by
  let p : Fin (l+2) := ⟨k.val-1,by have := k.isLt; omega⟩
  have hp : p.val+1 = k.val := by change k.val - 1 + 1 = k.val; omega
  have hRot : finRotate (l+2) p = k := by
    have h := finRotate_of_lt (show p.val < l+1 by have := k.isLt; omega)
    change finRotate (l+2) p = _ at h
    exact h.trans (Fin.ext hp)
  refine ⟨p,hp,?_⟩
  rw [← hRot]
  exact c.stitch p

/-- The first intervening occurrence of a private label is in an unpaired block. -/
theorem exists_unpaired_with_intervening_label (h : c.RepeatedEdges)
    {i j : Fin (l+2)} (hij : exactPair c.block i j) {u : V} (hu : c.InterveningPrivateLabel i j u) :
    ∃ k ∈ c.unpairedPositions, u ∈ (c.block k).vertices := by
  obtain ⟨hui,huL,huR,hExists⟩ := hu
  let S := (univ : Finset (Fin (l+2))).filter fun k ↦ i < k ∧ k < j ∧ u ∈ (c.block k).vertices
  have hS : S.Nonempty := by
    obtain ⟨k,hki,hkj,hku⟩ := hExists
    exact ⟨k,mem_filter.mpr ⟨mem_univ _,hki,hkj,hku⟩⟩
  let k := S.min' hS
  have hK : i < k ∧ k < j ∧ u ∈ (c.block k).vertices := (mem_filter.mp (min'_mem S hS)).2
  have hFirst {p : Fin (l+2)} (hip : i < p) (hpk : p < k) (hpu : u ∈ (c.block p).vertices) : False :=
    (not_lt_of_ge (min'_le S p (mem_filter.mpr ⟨mem_univ _,hip,hpk.trans hK.2.1,hpu⟩))) hpk
  refine ⟨k,c.mem_unpairedPositions.mpr ?_,hK.2.2⟩
  rintro ⟨q,hPair | hPair⟩
  · have hFor := (forward_return_of_exactPair h hPair).1
    have hU : u = (c.block k).left := hFor u hK.2.2 ⟨i,hK.1,hui⟩
    have hPos : 0 < k.val := by have : i.val < k.val := hK.1; omega
    obtain ⟨p,hp,hStitch⟩ := c.exists_predecessor_stitch hPos
    have hU' : u ∈ (c.block p).vertices := by rw [hU,← hStitch]; exact (c.block p).right_mem_vertices
    have hpK : p < k := by change p.val < k.val; omega
    have hip : i ≤ p := by
      have hh : i.val < k.val := hK.1
      change i.val ≤ p.val
      omega
    rcases lt_or_eq_of_le hip with hlt | he
    · exact hFirst hlt hpK hU'
    · exact huR (hU.trans (hStitch.symm.trans (congrArg (fun b ↦ (c.block b).right) he.symm)))
  · have he : (c.block q).vertices = (c.block k).vertices :=
      LabeledBlock.vertices_eq_of_graph_eq hPair.2.2.2.1
    have hUq : u ∈ (c.block q).vertices := he.symm ▸ hK.2.2
    rcases lt_trichotomy q i with hlt | heq | hgt
    · exact huL ((forward_return_of_exactPair h hij).1 u hui ⟨q,hlt,hUq⟩)
    · have hQ : exactPair c.block i k := heq ▸ hPair
      exact hK.2.1.ne (c.exactPair_right_unique hQ hij)
    · exact hFirst hgt hPair.1 hUq

/-- At most v marked pairs can be charged to the labels of each unpaired block. -/
theorem card_markedPairs_le (h : c.RepeatedEdges) {v : ℕ}
    (hV : ∀ i, (c.block i).shape.additionalVertices+2 ≤ v) :
    c.markedPairs.card ≤ v*c.unpairedPositions.card := by
  let S := c.unpairedPositions
  let Q := S.biUnion fun k ↦ ((c.block k).vertices).map ⟨Prod.mk k,fun _ _ h ↦ congrArg Prod.snd h⟩
  have hU (p : c.markedPairs) : ∃ u, c.InterveningPrivateLabel p.val.1 p.val.2 u :=
    (c.mem_markedPairs.mp p.property).2
  choose u hu using hU
  have hNext (p : c.markedPairs) : ∃ k ∈ S, u p ∈ (c.block k).vertices :=
    c.exists_unpaired_with_intervening_label h (c.mem_markedPairs.mp p.property).1 (hu p)
  choose k hk hku using hNext
  let f (p : c.markedPairs) : Q := ⟨(k p,u p),mem_biUnion.mpr ⟨k p,hk p,mem_map.mpr ⟨_,hku p,rfl⟩⟩⟩
  have hF : Function.Injective f := by
    intro p q he
    have hE : u p = u q := congrArg (fun z : Q ↦ z.val.2) he
    have hP := (c.mem_markedPairs.mp p.property).1
    have hQ := (c.mem_markedPairs.mp q.property).1
    have hEq : p.val.1 = q.val.1 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hlt
      · exact (hu q).2.1 ((forward_return_of_exactPair h hQ).1 _ (hu q).1
          ⟨p.val.1,hlt,hE ▸ (hu p).1⟩)
      · exact (hu p).2.1 ((forward_return_of_exactPair h hP).1 _ (hu p).1
          ⟨q.val.1,hlt,hE.symm ▸ (hu q).1⟩)
    apply Subtype.ext
    apply Prod.ext hEq
    exact c.exactPair_right_unique hP (hEq.symm ▸ hQ)
  have hCount := Fintype.card_le_of_injective f hF
  simp only [Fintype.card_coe] at hCount
  refine hCount.trans (card_biUnion_le.trans ?_)
  simp only [card_map,LabeledBlock.vertices,card_univ,Fintype.card_fin]
  exact (sum_le_sum (fun i _ ↦ hV i)).trans_eq (by rw [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm])

/-- All positions marked in the equality-pattern code. -/
noncomputable def markedPositions : Finset (Fin (l+2)) :=
  c.unpairedPositions ∪ c.markedPairs.image Prod.fst ∪ c.markedPairs.image Prod.snd

/-- Only a constant times the defect needs to be marked in the code. -/
theorem card_markedPositions_le (h : c.RepeatedEdges) {v : ℕ}
    (hV : ∀ i, (c.block i).shape.additionalVertices+2 ≤ v) :
    c.markedPositions.card ≤ (1+2*v)*(1+2*v^2+(2*v^2)^2)*c.defect := by
  have hp := c.card_markedPairs_le h hV
  have hu := c.card_unpairedPositions_le h hV
  calc
    _ ≤ c.unpairedPositions.card + c.markedPairs.card + c.markedPairs.card := by
      unfold markedPositions
      exact (card_union_le _ _).trans (Nat.add_le_add
        ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)) card_image_le)
    _ ≤ (1+2*v)*c.unpairedPositions.card :=
      (Nat.add_le_add (Nat.add_le_add_left hp _) hp).trans_eq (by ring)
    _ ≤ _ := (Nat.mul_le_mul_left _ hu).trans_eq (by ring)

end LovaszTheta.Independent.TraceBlocks
