module

public import LovaszTheta.EdgeSplit
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Deletions in a cycle

Deleting one vertex, or deleting the two endpoints of a cycle
edge, leaves a spanning path. Rotate the deleted vertices to
the initial positions of the cycle to exhibit that path.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

private lemma cycleGraph_translate_adj {n : ℕ} (d u v : Fin (n+2)) :
    (cycleGraph (n+2)).Adj (u+d) (v+d) ↔ (cycleGraph (n+2)).Adj u v := by
  rw [show cycleGraph (n+2) = circulantGraph {1} from cycleGraph_eq_circulantGraph (n+1)]
  exact circulantGraph_adj_translate

private lemma preconnected_cycleGraph_induce_prefix (n k : ℕ) :
    ((cycleGraph (n+2)).induce {v : Fin (n+2) | k ≤ v.val}).Preconnected := by
  let f (i : Fin (n+2-k)) : {v : Fin (n+2) // k ≤ v.val} :=
    ⟨⟨i.val+k,by have h := i.isLt; omega⟩,Nat.le_add_left _ _⟩
  have hAdj (i j : Fin (n+2-k)) (h : i.val+1 = j.val) :
      (cycleGraph (n+2)).Adj (f i).val (f j).val := by
    apply cycleGraph_adj'.mpr
    right
    have hle : (f i).val ≤ (f j).val := by
      change i.val+k ≤ j.val+k
      omega
    rw [Fin.sub_val_of_le hle]
    change j.val+k-(i.val+k) = 1
    omega
  let F : pathGraph (n+2-k) →g (cycleGraph (n+2)).induce {v : Fin (n+2) | k ≤ v.val} :=
    { toFun := f
      map_rel' := fun {i j} h ↦ by
        change (cycleGraph (n+2)).Adj (f i).val (f j).val
        rcases pathGraph_adj.mp h with hi | hj
        · exact hAdj i j hi
        · exact (hAdj j i hj).symm }
  have hs : Function.Surjective F := by
    rintro ⟨v,hv⟩
    have hV := v.isLt
    have hk : k ≤ v.val := hv
    refine ⟨⟨v.val-k,by omega⟩, Subtype.ext (Fin.ext ?_)⟩
    change v.val-k+k = v.val
    omega
  exact (preconnected_pathGraph _).map F hs

private lemma preconnected_cycleGraph_induce_translated (n k : ℕ) (d : Fin (n+2)) :
    ((cycleGraph (n+2)).induce {v : Fin (n+2) | k ≤ (v-d).val}).Preconnected := by
  let F : (cycleGraph (n+2)).induce {v : Fin (n+2) | k ≤ v.val} →g
      (cycleGraph (n+2)).induce {v : Fin (n+2) | k ≤ (v-d).val} :=
    { toFun := fun v ↦ ⟨v.val+d,by simpa only [Set.mem_ofPred_eq,add_sub_cancel_right] using v.property⟩
      map_rel' := fun {u v} h ↦ (cycleGraph_translate_adj d u.val v.val).mpr h }
  refine (preconnected_cycleGraph_induce_prefix n k).map F ?_
  rintro ⟨v,hv⟩
  exact ⟨⟨v-d,hv⟩,Subtype.ext (sub_add_cancel v d)⟩

/-- Every cycle with at least two vertices remains connected on
the remaining vertices after any single deletion. -/
theorem vertexDeletionConnected_cycleGraph (n : ℕ) :
    VertexDeletionConnected (cycleGraph (n+2)) := by
  intro d
  have he : {v : Fin (n+2) | v ≠ d} = {v : Fin (n+2) | 1 ≤ (v-d).val} := by
    ext v
    simp only [Set.mem_ofPred_eq,Nat.one_le_iff_ne_zero,ne_eq]
    have h0 : (v-d).val = 0 ↔ v = d := by
      exact ⟨fun h ↦ sub_eq_zero.mp (Fin.ext h),fun h ↦ by simp [h]⟩
    exact h0.not.symm
  rw [he]
  exact preconnected_cycleGraph_induce_translated n 1 d

private lemma preconnected_cycleGraph_remove_consecutive (n : ℕ) (d : Fin (n+2)) :
    ((cycleGraph (n+2)).induce {v | v ≠ d ∧ v ≠ d+1}).Preconnected := by
  have he : {v : Fin (n+2) | v ≠ d ∧ v ≠ d+1} =
      {v : Fin (n+2) | 2 ≤ (v-d).val} := by
    ext v
    simp only [Set.mem_ofPred_eq,ne_eq]
    have h0 : (v-d).val = 0 ↔ v = d :=
      ⟨fun h ↦ sub_eq_zero.mp (Fin.ext h),fun h ↦ by simp [h]⟩
    have hFirst : (v-d).val = 1 ↔ v-d = (1 : Fin (n+2)) := by
      simpa only [Fin.val_one] using (Fin.ext_iff (a := v-d) (b := (1 : Fin (n+2)))).symm
    have h1 : (v-d).val = 1 ↔ v = d+1 :=
      hFirst.trans (sub_eq_iff_eq_add.trans (by rw [add_comm (1 : Fin (n+2)) d]))
    simp only [← h0,← h1]
    omega
  rw [he]
  exact preconnected_cycleGraph_induce_translated n 2 d

/-- Deleting both vertices of a cycle edge leaves a path through
the remaining vertices. -/
theorem preconnected_cycleGraph_remove_adjacent {n : ℕ} {a b : Fin (n+2)}
    (h : (cycleGraph (n+2)).Adj a b) :
    ((cycleGraph (n+2)).induce {v | v ≠ a ∧ v ≠ b}).Preconnected := by
  rcases cycleGraph_adj.mp h with h | h
  · have he : a = b+1 := by simpa only [add_comm] using sub_eq_iff_eq_add.mp h
    rw [he]
    have hSet : {v | v ≠ b+1 ∧ v ≠ b} = {v | v ≠ b ∧ v ≠ b+1} := by ext; exact and_comm
    rw [hSet]
    exact preconnected_cycleGraph_remove_consecutive n b
  · have he : b = a+1 := by simpa only [add_comm] using sub_eq_iff_eq_add.mp h
    rw [he]
    exact preconnected_cycleGraph_remove_consecutive n a

end LovaszTheta.Independent
