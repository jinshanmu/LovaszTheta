module

public import LovaszTheta.TreeCovarianceEstimate

/-!
# Independence of the tree representative

Rooted isomorphisms transport leaf assignments, preserving all
node residues and the sign monomial. The field is consequently
defined on unordered tree types.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree.Isomorphism

variable {S T : RootedTree}

lemma leafEquiv_val (e : S.Isomorphism T) (u : S.Leaf) :
    (e.leafEquiv u).val = e.val u.val := rfl

lemma descendantLeaves_map (e : S.Isomorphism T) (v : S.Node) :
    (S.descendantLeaves v).map e.leafEquiv.toEmbedding = T.descendantLeaves (e.val v) := by
  ext w
  obtain ⟨u,rfl⟩ := e.leafEquiv.surjective w
  rw [mem_map]
  have h : Function.Semiconj e.val S.parent T.parent := e.property.2
  constructor
  · rintro ⟨z,hz,he⟩
    have hzu : z = u := e.leafEquiv.injective he
    obtain ⟨k,hk⟩ := (S.mem_descendantLeaves_iff v u).mp (hzu ▸ hz)
    exact (T.mem_descendantLeaves_iff _ _).mpr ⟨k, by
      rw [leafEquiv_val, ← h.iterate_right k, hk]⟩
  · intro hu
    obtain ⟨k,hk⟩ := (T.mem_descendantLeaves_iff _ _).mp hu
    rw [leafEquiv_val, ← h.iterate_right k] at hk
    exact ⟨u, (S.mem_descendantLeaves_iff v u).mpr ⟨k, e.val.injective hk⟩, rfl⟩

variable {n : ℕ}

lemma residue_comp_leafEquiv (e : S.Isomorphism T) (b : T.Leaf → ZMod n) (v : S.Node) :
    S.residue (b ∘ e.leafEquiv) v = T.residue b (e.val v) := by
  rw [residue, residue, ← e.descendantLeaves_map, sum_map]
  rfl

lemma admissible_comp_leafEquiv (e : S.Isomorphism T) (b : T.Leaf → ZMod n) :
    S.Admissible (b ∘ e.leafEquiv) ↔ T.Admissible b := by
  constructor
  · rintro ⟨hNZ,hInj⟩
    have h' (v : T.Node) : T.residue b v ≠ 0 := by
      obtain ⟨u,rfl⟩ := e.val.surjective v
      rw [← e.residue_comp_leafEquiv]
      exact hNZ u
    refine ⟨h', fun v w hvw ↦ ?_⟩
    obtain ⟨u,rfl⟩ := e.val.surjective v
    obtain ⟨z,rfl⟩ := e.val.surjective w
    apply congrArg e.val
    apply hInj
    rw [inversionClass_eq_iff] at hvw ⊢
    rwa [e.residue_comp_leafEquiv, e.residue_comp_leafEquiv]
  · rintro ⟨hNZ,hInj⟩
    have h' (v : S.Node) : S.residue (b ∘ e.leafEquiv) v ≠ 0 := by
      rw [e.residue_comp_leafEquiv]
      exact hNZ _
    refine ⟨h', fun v w hvw ↦ e.val.injective (hInj ?_)⟩
    rw [inversionClass_eq_iff] at hvw ⊢
    simpa only [e.residue_comp_leafEquiv] using hvw

/-- The induced bijection on admissible assignments. -/
noncomputable def assignmentEquiv (e : S.Isomorphism T) : T.Assignment n ≃ S.Assignment n :=
  (Equiv.arrowCongr e.leafEquiv.symm (Equiv.refl (ZMod n))).subtypeEquiv (fun b ↦
    (e.admissible_comp_leafEquiv b).symm)

lemma assignmentEquiv_val (e : S.Isomorphism T) (b : T.Assignment n) :
    (e.assignmentEquiv b).val = b.val ∘ e.leafEquiv := rfl

lemma signSupport_assignmentEquiv (e : S.Isomorphism T) (b : T.Assignment n) :
    S.signSupport (e.assignmentEquiv b) = T.signSupport b := by
  have h (v : S.Node) : S.classEmbedding (e.assignmentEquiv b) v = T.classEmbedding b (e.val v) := by
    apply (inversionClass_eq_iff ((e.assignmentEquiv b).property.choose v) (b.property.choose (e.val v))).mpr
    exact Or.inl (e.residue_comp_leafEquiv b.val v)
  ext s
  simp only [signSupport, mem_map, mem_univ, true_and, h]
  exact ⟨fun ⟨v,hv⟩ ↦ ⟨e.val v,hv⟩, fun ⟨w,hw⟩ ↦ ⟨e.val.symm w,by rwa [Equiv.apply_symm_apply]⟩⟩

/-- The field is independent of the choice of representative. -/
theorem field_eq [NeZero n] (e : S.Isomorphism T) (x : InversionClass n → Bool) (k : ZMod n) :
    S.field x k = T.field x k := by
  simp only [RootedTree.field_eq_sum, fieldNormalizer, e.leafCount_eq, e.card_automorphism_eq]
  congr 1
  symm
  refine Fintype.sum_equiv e.assignmentEquiv _ _ fun b ↦ ?_
  simp only [e.assignmentEquiv_val, e.signSupport_assignmentEquiv, e.residue_comp_leafEquiv, e.property.1]

end LovaszTheta.Circulant.RootedTree.Isomorphism
