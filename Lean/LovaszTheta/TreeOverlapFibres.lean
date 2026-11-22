module

public import LovaszTheta.TreeOverlap

/-!
# Counting overlap pairs with a specified symmetric difference

The role record specifies the residue at every unmatched node in
both trees. After fixing that record, the first tree's residues on
the complement of the overlap are fixed. Its leaves and the overlap
code then determine the second tree's leaves.
-/

@[expose] public section

open Finset
open scoped Classical symmDiff

namespace LovaszTheta.Circulant

variable {n : ℕ}

/-- The support of the product of the sign monomials of two assignments. -/
noncomputable def assignmentDifference (T S : RootedTree)
    (a : T.Assignment n) (b : S.Assignment n) : Finset (InversionClass n) :=
  T.signSupport a ∆ S.signSupport b

private lemma class_mem_signSupport (T : RootedTree) (a : T.Assignment n) (v : T.Node) :
    T.classEmbedding a v ∈ T.signSupport a :=
  mem_map.mpr ⟨v, mem_univ _, rfl⟩

private lemma residue_mem_class (T : RootedTree) (a : T.Assignment n) (v : T.Node) :
    T.residue a.val v ∈ (T.classEmbedding a v).val := mem_insert_self _ _

private lemma assignmentDifference_card_le (T S : RootedTree)
    (a : T.Assignment n) (b : S.Assignment n) :
    (assignmentDifference T S a b).card ≤ T.nodeCount + S.nodeCount := by
  unfold assignmentDifference
  exact (card_le_card symmDiff_subset_union).trans (by
    simpa only [RootedTree.signSupport_card] using card_union_le (T.signSupport a) (S.signSupport b))

private lemma card_class_union_le (I : Finset (InversionClass n)) :
    (I.biUnion fun c ↦ c.val).card ≤ 2 * I.card := by
  calc
    _ ≤ ∑ c ∈ I, c.val.card := card_biUnion_le
    _ ≤ ∑ _c ∈ I, 2 := sum_le_sum fun c _ ↦ inversionClass_card_le c
    _ = _ := by simp [mul_comm]

variable [NeZero n]

/-- The largest support fiber for one overlap pattern is controlled by
the rank of its complementary rows and the possible unmatched residues. -/
theorem card_overlap_difference_pairs_le (T S : RootedTree) (c : OverlapCode T S)
    (I : Finset (InversionClass n)) :
    Fintype.card {ab : T.Assignment n × S.Assignment n //
      overlapCode T S ab.1 ab.2 = c ∧ assignmentDifference T S ab.1 ab.2 = I} ≤
      (1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) *
      n ^ (Fintype.card T.Leaf - leafRowRank T.leafRow (sharedRoles c)ᶜ) := by
  let X := {ab : T.Assignment n × S.Assignment n //
    overlapCode T S ab.1 ab.2 = c ∧ assignmentDifference T S ab.1 ab.2 = I}
  change Fintype.card X ≤ _
  by_cases hX : Nonempty X
  · obtain ⟨ab₀⟩ := hX
    let L := I.biUnion fun b ↦ b.val
    have hI : I.card ≤ T.nodeCount + S.nodeCount := ab₀.property.2 ▸
      assignmentDifference_card_le T S ab₀.val.1 ab₀.val.2
    have hL : L.card ≤ 2 * (T.nodeCount + S.nodeCount) :=
      (card_class_union_le I).trans (Nat.mul_le_mul_left _ hI)
    have hFirst (ab : X) (u : T.Node)
        (hu : T.classEmbedding ab.val.1 u ∉ S.signSupport ab.val.2) :
        T.residue ab.val.1.val u ∈ L := by
      have hClass : T.classEmbedding ab.val.1 u ∈ assignmentDifference T S ab.val.1 ab.val.2 :=
        mem_symmDiff.mpr (Or.inl ⟨class_mem_signSupport T ab.val.1 u, hu⟩)
      have hMem : T.classEmbedding ab.val.1 u ∈ I :=
        (congrArg (fun J : Finset (InversionClass n) ↦ T.classEmbedding ab.val.1 u ∈ J) ab.property.2).mp hClass
      exact mem_biUnion.mpr ⟨T.classEmbedding ab.val.1 u, hMem,
        residue_mem_class T ab.val.1 u⟩
    have hSecond (ab : X) (v : S.Node)
        (hv : S.classEmbedding ab.val.2 v ∉ T.signSupport ab.val.1) :
        S.residue ab.val.2.val v ∈ L := by
      have hClass : S.classEmbedding ab.val.2 v ∈ assignmentDifference T S ab.val.1 ab.val.2 :=
        mem_symmDiff.mpr (Or.inr ⟨class_mem_signSupport S ab.val.2 v, hv⟩)
      have hMem : S.classEmbedding ab.val.2 v ∈ I :=
        (congrArg (fun J : Finset (InversionClass n) ↦ S.classEmbedding ab.val.2 v ∈ J) ab.property.2).mp hClass
      exact mem_biUnion.mpr ⟨S.classEmbedding ab.val.2 v, hMem,
        residue_mem_class S ab.val.2 v⟩
    let C := (T.Node ⊕ S.Node) → Option (↥L)
    let record (ab : X) : C :=
      Sum.elim
        (fun u ↦ if hu : T.classEmbedding ab.val.1 u ∉ S.signSupport ab.val.2 then
          some ⟨T.residue ab.val.1.val u, hFirst ab u hu⟩ else none)
        (fun v ↦ if hv : S.classEmbedding ab.val.2 v ∉ T.signSupport ab.val.1 then
          some ⟨S.residue ab.val.2.val v, hSecond ab v hv⟩ else none)
    let recover (rec : C) (t : T.Node ⊕ S.Node) : ZMod n :=
      (rec t).elim 0 Subtype.val
    have hDecode₁ (ab : X) (u : T.Node) (hu : u ∈ (sharedRoles c)ᶜ) :
        recover (record ab) (.inl u) = T.residue ab.val.1.val u := by
      have hUnmatched : T.classEmbedding ab.val.1 u ∉ S.signSupport ab.val.2 := fun hm ↦
        (mem_compl.mp hu) (ab.property.1 ▸ (sharedRoles_mem_iff ab.val.1 ab.val.2 u).mpr hm)
      simp [recover, record, hUnmatched]
    have hDecode₂ (ab : X) (v : S.Node)
        (hv : S.classEmbedding ab.val.2 v ∉ T.signSupport ab.val.1) :
        recover (record ab) (.inr v) = S.residue ab.val.2.val v := by
      simp [recover, record, hv]
    let Y (rec : C) :=
      {a : T.Leaf → ZMod n //
        ∀ u ∈ (sharedRoles c)ᶜ, T.residue a u = recover rec (.inl u)}
    let enc (ab : X) : Σ rec : C, Y rec :=
      ⟨record ab, ⟨ab.val.1.val, fun u hu ↦ (hDecode₁ ab u hu).symm⟩⟩
    have hInj : Function.Injective enc := by
      intro x y he
      have hRecord : record x = record y := congrArg Sigma.fst he
      have ha : x.val.1 = y.val.1 :=
        Subtype.ext (congrArg (fun z : Σ rec : C, Y rec ↦ z.2.val) he)
      have hCode : overlapCode T S x.val.1 x.val.2 = overlapCode T S y.val.1 y.val.2 :=
        x.property.1.trans y.property.1.symm
      have hb : x.val.2 = y.val.2 := by
        apply Subtype.ext
        funext i
        rw [← S.residue_leaf x.val.2.val i, ← S.residue_leaf y.val.2.val i]
        by_cases hx : S.classEmbedding x.val.2 i.val ∈ T.signSupport x.val.1
        · obtain ⟨u, _, hu⟩ := mem_map.mp hx
          obtain ⟨o, hxMatch⟩ := overlapCode_matches hu
          have hyMatch : overlapCode T S y.val.1 y.val.2 u = some (i.val, o) :=
            (congrFun hCode u).symm.trans hxMatch
          have hxMem : u ∈ sharedRoles (overlapCode T S x.val.1 x.val.2) :=
            (sharedRoles_mem_iff x.val.1 x.val.2 u).mpr ((class_eq_of_overlapCode_some hxMatch).symm ▸
              class_mem_signSupport S x.val.2 i.val)
          have hyMem : u ∈ sharedRoles (overlapCode T S y.val.1 y.val.2) := hCode ▸ hxMem
          have hSame := ((matchedResidue_eq hxMem).symm.trans
            (congrArg (fun a : T.Assignment n ↦ T.residue a.val u) ha)).trans
              (matchedResidue_eq hyMem)
          cases o <;> simpa [matchedResidue, hxMatch, hyMatch] using hSame
        · have hy : S.classEmbedding y.val.2 i.val ∉ T.signSupport y.val.1 := by
            intro hm
            obtain ⟨u, _, hu⟩ := mem_map.mp hm
            obtain ⟨o, hyMatch⟩ := overlapCode_matches hu
            have hxMatch : overlapCode T S x.val.1 x.val.2 u = some (i.val, o) :=
              (congrFun hCode u).trans hyMatch
            exact hx ((class_eq_of_overlapCode_some hxMatch) ▸ class_mem_signSupport T x.val.1 u)
          rw [← hDecode₂ x i.val hx, ← hDecode₂ y i.val hy, hRecord]
      exact Subtype.ext (Prod.ext ha hb)
    have hC : Fintype.card C ≤
        (1 + 2 * (T.nodeCount + S.nodeCount)) ^ (T.nodeCount + S.nodeCount) := by
      rw [Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      exact Nat.pow_le_pow_left (by omega) _
    calc
      Fintype.card X ≤ Fintype.card (Σ rec : C, Y rec) := Fintype.card_le_of_injective enc hInj
      _ = ∑ rec : C, Fintype.card (Y rec) := Fintype.card_sigma
      _ ≤ ∑ _rec : C, n ^ (Fintype.card T.Leaf - leafRowRank T.leafRow (sharedRoles c)ᶜ) :=
        sum_le_sum fun rec _ ↦ T.card_prescribed_residues_le (sharedRoles c)ᶜ
          (fun u ↦ recover rec (.inl u))
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, card_univ]
        exact Nat.mul_le_mul_right _ hC
  · have : IsEmpty X := not_nonempty_iff.mp hX
    rw [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

end LovaszTheta.Circulant
