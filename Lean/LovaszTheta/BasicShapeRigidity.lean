module

public import LovaszTheta.BasicShapes
public import LovaszTheta.ShapeIsomorphism

/-!
# Rigidity of the oriented basic blocks

The unique spanning cycle forces a boundary-preserving
isomorphism to preserve every successive vertex in the
cycle order.
-/

@[expose] public section

open SimpleGraph

namespace LovaszTheta.Independent

private lemma eq_add_one_of_val_succ {n : ℕ} {i j : Fin (n+2)} (h : i.val+1 = j.val) : j = i+1 := by
  apply Fin.ext
  rw [Fin.val_add,Fin.val_one,h,Nat.mod_eq_of_lt j.isLt]

/-- A permutation preserving the cycle and fixing an ordered adjacent
pair at zero and one is the identity. -/
theorem cyclePermutation_eq_refl {n : ℕ} (e : Equiv.Perm (Fin (n+2)))
    (hE : ∀ {u v}, (cycleGraph (n+2)).Adj u v → (cycleGraph (n+2)).Adj (e u) (e v))
    (h₀ : e 0 = 0) (h₁ : e 1 = 1) : e = Equiv.refl _ := by
  have hFix (k : ℕ) : ∀ hk : k < n+2, e ⟨k,hk⟩ = ⟨k,hk⟩ := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      by_cases hSmall : k ≤ 1
      · have h : k = 0 ∨ k = 1 := by omega
        rcases h with rfl | rfl
        · exact h₀
        · exact h₁
      · let z : Fin (n+2) := ⟨k,hk⟩
        let p : Fin (n+2) := ⟨k-1,by omega⟩
        let q : Fin (n+2) := ⟨k-2,by omega⟩
        have hp : e p = p := ih (k-1) (by omega) p.isLt
        have hq : e q = q := ih (k-2) (by omega) q.isLt
        have hz : z = p+1 := eq_add_one_of_val_succ (by change k-1+1=k; omega)
        have hqp : p = q+1 := eq_add_one_of_val_succ (by change k-2+1=k-1; omega)
        have hAdj : (cycleGraph (n+2)).Adj p z :=
          cycleGraph_adj.mpr (Or.inr (by rw [hz,add_comm p 1,add_sub_cancel_right]))
        have h := hE hAdj
        rw [hp] at h
        rcases cycleGraph_adj.mp h with h | h
        · have hOld := sub_eq_iff_eq_add.mp h
          rw [hqp,add_comm (1 : Fin (n+2)) (e z)] at hOld
          have he : q = e z := add_right_cancel hOld
          have heq : z = q := e.injective (he.symm.trans hq.symm)
          have hVal := congrArg Fin.val heq
          change k = k-2 at hVal
          omega
        · exact (sub_eq_iff_eq_add.mp h).trans ((add_comm 1 p).trans hz.symm)
  exact Equiv.ext fun z ↦ hFix z.val z.isLt

namespace BasicShape

/-- An automorphism fixing both boundaries of a basic block fixes every vertex. -/
theorem boundary_automorphism_eq_refl (S : BasicShape) (e : S.toShape.Isomorphism S.toShape) :
    e.graphIso.toEquiv = Equiv.refl _ :=
  cyclePermutation_eq_refl e.graphIso.toEquiv (fun h ↦
    cycle_adj_of_spanning_cycle S.noncrossing e.graphIso.toEquiv
      (fun h ↦ e.graphIso.map_rel_iff.mpr (S.cycle_le h)) h) e.map_left e.map_right

/-- The cycle coordinates give a unique basic shape in each ordered isomorphism class. -/
theorem eq_of_isomorphism {S T : BasicShape} (e : S.toShape.Isomorphism T.toShape) : S = T := by
  have hCount := Fintype.card_congr e.graphIso.toEquiv
  change Fintype.card (Fin (S.additionalVertices+2)) = Fintype.card (Fin (T.additionalVertices+2)) at hCount
  simp only [Fintype.card_fin] at hCount
  have hn : S.additionalVertices = T.additionalVertices := by omega
  obtain ⟨n,G,hG,hNG⟩ := S
  obtain ⟨k,H,hH,hNH⟩ := T
  change n = k at hn
  subst k
  let p : Equiv.Perm (Fin (n+2)) := e.graphIso.toEquiv
  have hp : p = Equiv.refl _ :=
    cyclePermutation_eq_refl p (fun h ↦ cycle_adj_of_spanning_cycle hNH p
      (fun h ↦ e.graphIso.map_rel_iff.mpr (hG h)) h) e.map_left e.map_right
  have hEq : G = H := by
    ext u v
    have h := e.graphIso.map_rel_iff (a := u) (b := v)
    change H.Adj (p u) (p v) ↔ G.Adj u v at h
    rwa [hp,Equiv.refl_apply,Equiv.refl_apply,iff_comm] at h
  subst H
  rfl

end BasicShape

end LovaszTheta.Independent
