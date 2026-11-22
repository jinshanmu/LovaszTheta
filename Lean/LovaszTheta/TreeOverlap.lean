module

public import LovaszTheta.TreeRankPartition

/-!
# Matching the shared classes of two tree assignments

An overlap pattern records the node roles and orientations of the
shared inversion classes. Once the second assignment is fixed, the
pattern fixes the residues on the shared roles of the first tree.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

/-- For each node of the first tree, the matched node of the second
tree and its relative orientation, when the class is shared. -/
abbrev OverlapCode (T S : RootedTree) := T.Node → Option (S.Node × Bool)

/-- The first tree's roles belonging to the overlap. -/
noncomputable def sharedRoles {T S : RootedTree} (c : OverlapCode T S) : Finset T.Node :=
  univ.filter fun u ↦ (c u).isSome

variable {n : ℕ}

/-- Recover the residue on the first tree at a shared role from the
second tree's assignment and the relative orientation of the match. -/
noncomputable def matchedResidue {T S : RootedTree} (c : OverlapCode T S)
    (b : S.Assignment n) (u : T.Node) : ZMod n :=
  match c u with
  | none => 0
  | some (v, orientation) => if orientation then S.residue b.val v else - S.residue b.val v

/-- The overlap code of two admissible assignments. A singleton class
uses the positive orientation. -/
noncomputable def overlapCode (T S : RootedTree) (a : T.Assignment n) (b : S.Assignment n) :
    OverlapCode T S :=
  fun u ↦ if h : ∃ v, T.classEmbedding a u = S.classEmbedding b v then
    some (h.choose, decide (T.residue a.val u = S.residue b.val h.choose))
  else none

lemma sharedRoles_mem_iff {T S : RootedTree} (a : T.Assignment n) (b : S.Assignment n) (u : T.Node) :
    u ∈ sharedRoles (overlapCode T S a b) ↔ T.classEmbedding a u ∈ S.signSupport b := by
  have hMem : T.classEmbedding a u ∈ S.signSupport b ↔
      ∃ v, T.classEmbedding a u = S.classEmbedding b v := by
    simp only [RootedTree.signSupport, mem_map, mem_univ, true_and]
    exact exists_congr (fun _ ↦ eq_comm)
  rw [hMem]
  by_cases h : ∃ v, T.classEmbedding a u = S.classEmbedding b v
  · simp [sharedRoles, overlapCode, h]
  · simp [sharedRoles, overlapCode, h]

lemma overlapCode_matches {T S : RootedTree} {a : T.Assignment n} {b : S.Assignment n}
    {u : T.Node} {v : S.Node} (h : T.classEmbedding a u = S.classEmbedding b v) :
    ∃ orientation : Bool, overlapCode T S a b u = some (v, orientation) := by
  have hExists : ∃ q, T.classEmbedding a u = S.classEmbedding b q := ⟨v, h⟩
  have hRole : hExists.choose = v :=
    (S.classEmbedding b).injective (hExists.choose_spec.symm.trans h)
  exact ⟨decide (T.residue a.val u = S.residue b.val v),
    by simp only [overlapCode, dite_eq_left hExists, hRole]⟩

lemma class_eq_of_overlapCode_some {T S : RootedTree} {a : T.Assignment n} {b : S.Assignment n}
    {u : T.Node} {v : S.Node} {orientation : Bool}
    (h : overlapCode T S a b u = some (v, orientation)) :
    T.classEmbedding a u = S.classEmbedding b v := by
  unfold overlapCode at h
  split_ifs at h with he
  have hV := congrArg Prod.fst (Option.some.inj h)
  exact he.choose_spec.trans (congrArg (S.classEmbedding b) hV)

lemma matchedResidue_eq {T S : RootedTree} {a : T.Assignment n} {b : S.Assignment n}
    {u : T.Node} (hu : u ∈ sharedRoles (overlapCode T S a b)) :
    T.residue a.val u = matchedResidue (overlapCode T S a b) b u := by
  obtain ⟨v, hv⟩ := (mem_map.mp ((sharedRoles_mem_iff a b u).mp hu))
  have hExists : ∃ q, T.classEmbedding a u = S.classEmbedding b q := ⟨v, hv.2.symm⟩
  have hSigned := (inversionClass_eq_iff (a.property.choose u)
    (b.property.choose hExists.choose)).mp hExists.choose_spec
  simp only [matchedResidue, overlapCode, dite_eq_left hExists, decide_eq_true_eq]
  split_ifs with h
  · exact h
  · exact hSigned.resolve_left h

variable [NeZero n]

/-- The number of assignment pairs with a fixed overlap pattern is bounded by
choosing the second assignment first and then using the rank on the shared
roles of the first tree. -/
theorem card_overlap_pairs_le (T S : RootedTree) (c : OverlapCode T S) :
    Fintype.card {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c} ≤
      n ^ Fintype.card S.Leaf * n ^ (Fintype.card T.Leaf - leafRowRank T.leafRow (sharedRoles c)) := by
  let X := {ab : T.Assignment n × S.Assignment n // overlapCode T S ab.1 ab.2 = c}
  let Y (b : S.Assignment n) :=
    {x : T.Leaf → ZMod n // ∀ u ∈ sharedRoles c, T.residue x u = matchedResidue c b u}
  have hEncode (ab : X) (u : T.Node) (hu : u ∈ sharedRoles c) :
      T.residue ab.val.1.val u = matchedResidue c ab.val.2 u := by
    have hc := ab.property
    have hMem : u ∈ sharedRoles (overlapCode T S ab.val.1 ab.val.2) := hc.symm ▸ hu
    exact (matchedResidue_eq hMem).trans (congrArg (fun p ↦ matchedResidue p ab.val.2 u) hc)
  let map (ab : X) : Σ b : S.Assignment n, Y b := ⟨ab.val.2, ⟨ab.val.1.val, hEncode ab⟩⟩
  have hInj : Function.Injective map := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : Σ b : S.Assignment n, Y b ↦ z.2.val) he)
    · exact congrArg Sigma.fst he
  calc
    Fintype.card X ≤ Fintype.card (Σ b : S.Assignment n, Y b) := Fintype.card_le_of_injective map hInj
    _ = ∑ b : S.Assignment n, Fintype.card (Y b) := Fintype.card_sigma
    _ ≤ ∑ _b : S.Assignment n, n ^ (Fintype.card T.Leaf - leafRowRank T.leafRow (sharedRoles c)) :=
      sum_le_sum fun b _ ↦ T.card_prescribed_residues_le (sharedRoles c) (matchedResidue c b)
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul, card_univ]
      apply Nat.mul_le_mul_right
      have h := Fintype.card_le_of_injective (fun b : S.Assignment n ↦ b.val) Subtype.val_injective
      rwa [Fintype.card_fun, ZMod.card] at h

end LovaszTheta.Circulant
