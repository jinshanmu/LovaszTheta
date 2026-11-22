module

public import LovaszTheta.CycleFrames
public import LovaszTheta.ShapeIsomorphism
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Reversal and path order for basic shapes

The reversed shape numbers the same cycle from the right boundary.
In path order, the left boundary is zero and the right is the last
vertex. The cycle edge between the boundaries closes the spanning path.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

private lemma neg_val_of_ne_zero {n : ℕ} {i : Fin (n+2)} (h : i ≠ 0) :
    (-i).val = n+2-i.val := by
  rw [Fin.val_neg]
  simp only [h,ite_false]

theorem Noncrossing.comap_neg {n : ℕ} {G : SimpleGraph (Fin (n+2))} (hG : Noncrossing G) :
    Noncrossing (G.comap fun i ↦ -i) := by
  intro a u b v hau hub hbv hab huv
  change G.Adj (-a) (-b) at hab
  change G.Adj (-u) (-v) at huv
  have hv : v ≠ 0 := Fin.ne_of_gt (Fin.zero_le b |>.trans_lt hbv)
  have hb : b ≠ 0 := Fin.ne_of_gt (Fin.zero_le u |>.trans_lt hub)
  have hu : u ≠ 0 := Fin.ne_of_gt (Fin.zero_le a |>.trans_lt hau)
  have hvb : -v < -b := by
    change (-v).val < (-b).val
    rw [neg_val_of_ne_zero hv,neg_val_of_ne_zero hb]
    have h₁ := v.isLt
    have h₂ : b.val < v.val := hbv
    omega
  have hbu : -b < -u := by
    change (-b).val < (-u).val
    rw [neg_val_of_ne_zero hb,neg_val_of_ne_zero hu]
    have h₁ := b.isLt
    have h₂ : u.val < b.val := hub
    omega
  by_cases ha : a = 0
  · have h₀ : -a < -v := by rw [ha,neg_zero]; exact Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hv)
    exact hG h₀ hvb hbu hab huv.symm
  · have hua : -u < -a := by
      change (-u).val < (-a).val
      rw [neg_val_of_ne_zero hu,neg_val_of_ne_zero ha]
      have h₁ := u.isLt
      have h₂ : a.val < u.val := hau
      omega
    exact hG hvb hbu hua huv.symm hab.symm

theorem Noncrossing.comap_rotate {n : ℕ} {G : SimpleGraph (Fin (n+2))} (hG : Noncrossing G) :
    Noncrossing (G.comap (finRotate (n+2))) := by
  intro a u b v hau hub hbv hab huv
  let r := finRotate (n+2)
  change G.Adj (r a) (r b) at hab
  change G.Adj (r u) (r v) at huv
  have hn {i j : Fin (n+2)} (h : i < j) : i ≠ Fin.last (n+1) :=
    (h.trans_le (Fin.le_last j)).ne
  have hf {i j : Fin (n+2)} (h : i < j) (hj : j ≠ Fin.last (n+1)) : r i < r j := by
    change (r i).val < (r j).val
    rw [coe_finRotate_of_ne_last (hn h),coe_finRotate_of_ne_last hj]
    exact Nat.add_lt_add_right h 1
  by_cases hv : v = Fin.last (n+1)
  · have h₀ : r v < r a := by
      change (r v).val < (r a).val
      rw [show r v = 0 by rw [hv]; exact finRotate_last,coe_finRotate_of_ne_last (hn hau)]
      exact Nat.zero_lt_succ _
    exact hG h₀ (hf hau (hn hub)) (hf hub (hn hbv)) huv.symm hab
  · exact hG (hf hau (hn hub)) (hf hub (hn hbv)) (hf hbv hv) hab huv

private lemma cycle_neg_adj_iff {n : ℕ} (a b : Fin (n+2)) :
    (cycleGraph (n+2)).Adj (-a) (-b) ↔ (cycleGraph (n+2)).Adj a b := by
  rw [cycleGraph_adj,cycleGraph_adj,show -a- -b = b-a by abel,
    show -b- -a = a-b by abel,or_comm]

lemma cycle_reverse_adj_iff {n : ℕ} (a b : Fin (n+2)) :
    (cycleGraph (n+2)).Adj (1-a) (1-b) ↔ (cycleGraph (n+2)).Adj a b := by
  rw [cycleGraph_adj,cycleGraph_adj,show 1-a-(1-b) = b-a by abel,
    show 1-b-(1-a) = a-b by abel,or_comm]

namespace BasicShape

/-- The same block with its boundaries exchanged and its cycle reoriented. -/
def reverse (T : BasicShape) : BasicShape where
  additionalVertices := T.additionalVertices
  graph := T.graph.comap (fun i ↦ 1-i)
  cycle_le := fun a b h ↦ T.cycle_le ((cycle_reverse_adj_iff a b).mpr h)
  noncrossing := by
    have h : (fun i : Fin (T.additionalVertices+2) ↦ 1-i) =
        (fun i ↦ finRotate (T.additionalVertices+2) (-i)) := by
      funext i
      rw [finRotate_apply]
      abel
    rw [h]
    exact fun {a u b v} ↦ @Noncrossing.comap_neg _ _
      (@Noncrossing.comap_rotate _ _ T.noncrossing) a u b v

lemma eq_of_graph_heq {T U : BasicShape} (hSize : T.additionalVertices = U.additionalVertices)
    (hGraph : HEq T.graph U.graph) : T = U := by
  cases T with
  | mk n G hG hN =>
    cases U with
    | mk m H hH hM =>
      change n = m at hSize
      subst m
      have he : G = H := eq_of_heq hGraph
      subst H
      rfl

@[simp]
lemma reverse_reverse (T : BasicShape) : T.reverse.reverse = T := by
  apply eq_of_graph_heq (T := T.reverse.reverse) (U := T) rfl
  have he : (T.graph.comap (fun i : Fin (T.additionalVertices+2) ↦ 1-i)).comap
      (fun i : Fin (T.additionalVertices+2) ↦ 1-i) = T.graph := by
    ext a b
    change T.graph.Adj (1-(1-a)) (1-(1-b)) ↔ T.graph.Adj a b
    rw [sub_sub_cancel,sub_sub_cancel]
  exact heq_of_eq he

/-- Reversing the canonical block implements transposition of its graph matrix. -/
def reverseIsomorphism (T : BasicShape) : T.reverse.toShape.Isomorphism T.toShape.reverse where
  graphIso :=
    { toEquiv := (Equiv.neg (Fin (T.additionalVertices+2))).trans (Equiv.addRight 1)
      map_rel_iff' := by
        intro a b
        change Fin (T.additionalVertices+2) at a b
        change T.graph.Adj (-a+1) (-b+1) ↔ T.graph.Adj (1-a) (1-b)
        rw [show -a+1 = 1-a by abel,show -b+1 = 1-b by abel] }
  map_left := by change -(0 : Fin (T.additionalVertices+2))+1 = 1; simp
  map_right := by change -(1 : Fin (T.additionalVertices+2))+1 = 0; simp

/-- The graph numbered along the path between the boundaries. -/
def pathGraph (T : BasicShape) : SimpleGraph (Fin (T.additionalVertices+2)) :=
  T.graph.comap (fun i ↦ -i)

lemma pathGraph_noncrossing (T : BasicShape) : Noncrossing T.pathGraph :=
  fun {a u b v} ↦ @Noncrossing.comap_neg _ _ T.noncrossing a u b v

lemma pathGraph_adj_of_succ (T : BasicShape) {a b : Fin (T.additionalVertices+2)}
    (h : b.val = a.val+1) : T.pathGraph.Adj a b := by
  apply T.cycle_le
  apply (cycle_neg_adj_iff a b).mpr
  apply cycleGraph_adj'.mpr
  exact Or.inr (by rw [Fin.sub_val_of_le (show a ≤ b by change a.val ≤ b.val; omega),h,Nat.add_sub_cancel_left])

lemma pathGraph_adj_endpoints (T : BasicShape) :
    T.pathGraph.Adj 0 (Fin.last (T.additionalVertices+1)) := by
  change T.graph.Adj (-0) (-(Fin.last (T.additionalVertices+1)))
  rw [neg_zero,Fin.neg_last]
  exact T.toShape_left_adj_right

end BasicShape

end LovaszTheta.Independent
