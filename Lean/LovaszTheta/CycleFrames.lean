module

public import LovaszTheta.BasicShapeRigidity

/-!
# Changing the boundary of a basic cycle

A cycle permutation is fixed by the images of its ordered
boundaries. The explicit rotation or reflection gives the
return orientation determined by the two boundary labels.
-/

@[expose] public section

open SimpleGraph
open scoped Classical

namespace LovaszTheta.Independent

/-- The oriented cycle coordinates based on the ordered edge (a,b). -/
def cycleFrame {n : ℕ} (a b : Fin (n+2)) : Equiv.Perm (Fin (n+2)) :=
  if b = a+1 then Equiv.addRight a else (Equiv.neg _).trans (Equiv.addRight a)

@[simp]
lemma cycleFrame_zero {n : ℕ} (a b : Fin (n+2)) : cycleFrame a b 0 = a := by
  unfold cycleFrame
  split_ifs
  · change 0+a = _
    exact zero_add a
  · change -0+a = _
    simp only [neg_zero,zero_add]

lemma cycleFrame_one {n : ℕ} {a b : Fin (n+2)} (h : (cycleGraph (n+2)).Adj a b) :
    cycleFrame a b 1 = b := by
  unfold cycleFrame
  split_ifs with h₁
  · change 1+a = b
    exact (add_comm 1 a).trans h₁.symm
  · change -1+a = b
    rcases cycleGraph_adj.mp h with h' | h'
    · rw [show (-1 : Fin (n+2)) = -(a-b) by rw [h']]
      abel
    · exact (h₁ ((sub_eq_iff_eq_add.mp h').trans (add_comm 1 a))).elim

lemma cycleFrame_adj_iff {n : ℕ} (a b x y : Fin (n+2)) :
    (cycleGraph (n+2)).Adj (cycleFrame a b x) (cycleFrame a b y) ↔ (cycleGraph (n+2)).Adj x y := by
  rw [cycleGraph_adj,cycleGraph_adj]
  unfold cycleFrame
  split_ifs
  · change (x+a-(y+a) = 1 ∨ y+a-(x+a) = 1) ↔ x-y = 1 ∨ y-x = 1
    rw [show x+a-(y+a) = x-y by abel,show y+a-(x+a) = y-x by abel]
  · change (-x+a-(-y+a) = 1 ∨ -y+a-(-x+a) = 1) ↔ x-y = 1 ∨ y-x = 1
    rw [show -x+a-(-y+a) = y-x by abel,show -y+a-(-x+a) = x-y by abel,or_comm]

/-- The return orientation is a function only of the ordered pair of endpoints. -/
theorem cyclePermutation_eq_cycleFrame {n : ℕ} (e : Equiv.Perm (Fin (n+2)))
    (he : ∀ {a b}, (cycleGraph (n+2)).Adj a b → (cycleGraph (n+2)).Adj (e a) (e b)) :
    e = cycleFrame (e 0) (e 1) := by
  let f := cycleFrame (e 0) (e 1)
  have h₀ : f 0 = e 0 := cycleFrame_zero _ _
  have h₁ : f 1 = e 1 := cycleFrame_one (he (cycleGraph_adj.mpr (Or.inr (sub_zero 1))))
  have hf (u v : Fin (n+2)) : (cycleGraph (n+2)).Adj (f u) (f v) ↔ (cycleGraph (n+2)).Adj u v :=
    cycleFrame_adj_iff _ _ _ _
  have hInv (u v : Fin (n+2)) (h : (cycleGraph (n+2)).Adj u v) :
      (cycleGraph (n+2)).Adj (f.symm u) (f.symm v) :=
    (hf (f.symm u) (f.symm v)).mp (by simpa only [Equiv.apply_symm_apply] using h)
  have hId := cyclePermutation_eq_refl (e.trans f.symm) (fun h ↦ hInv _ _ (he h))
    (by rw [Equiv.trans_apply,← h₀,Equiv.symm_apply_apply])
    (by rw [Equiv.trans_apply,← h₁,Equiv.symm_apply_apply])
  apply Equiv.ext
  intro u
  have hU : f.symm (e u) = u := congrFun (congrArg Equiv.toFun hId) u
  exact f.symm.injective (hU.trans (f.symm_apply_apply _).symm)

end LovaszTheta.Independent
