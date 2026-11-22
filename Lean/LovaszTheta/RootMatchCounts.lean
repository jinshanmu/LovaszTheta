module

public import LovaszTheta.RootedSignedMatches

/-!
# Counting the preserving root-to-root matches

Each preserving root-to-root match is a rooted isomorphism and a
choice of a common sign. If the trees are isomorphic, composition
with a fixed isomorphism identifies the isomorphisms with the
automorphisms of the source tree.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

namespace RootedTree

/-- A bijection of the nodes preserving the root and parent map. -/
abbrev Isomorphism (S T : RootedTree) :=
  {e : S.Node ≃ T.Node // e S.root = T.root ∧ ∀ v, e (S.parent v) = T.parent (e v)}

noncomputable instance (S T : RootedTree) : Fintype (S.Isomorphism T) := Fintype.ofFinite _

namespace Isomorphism

variable {R S T : RootedTree}

/-- Invert a rooted isomorphism. -/
def symm (e : S.Isomorphism T) : T.Isomorphism S :=
  ⟨e.val.symm, (e.val.symm_apply_eq).mpr e.property.1.symm, fun v ↦ by
    apply e.val.injective
    rw [e.val.apply_symm_apply, e.property.2, e.val.apply_symm_apply]⟩

/-- Compose rooted isomorphisms. -/
def trans (e : R.Isomorphism S) (f : S.Isomorphism T) : R.Isomorphism T :=
  ⟨e.val.trans f.val, by simp only [Equiv.trans_apply, e.property.1, f.property.1],
    fun v ↦ by simp only [Equiv.trans_apply, e.property.2, f.property.2]⟩

end Isomorphism

/-- A fixed rooted isomorphism identifies the number of isomorphisms
with the number of automorphisms. -/
theorem card_isomorphism_eq_card_automorphism {S T : RootedTree}
    (e : S.Isomorphism T) :
    Fintype.card (S.Isomorphism T) = Fintype.card T.Automorphism := by
  let F : S.Isomorphism T ≃ T.Automorphism :=
    { toFun := fun f ↦ e.symm.trans f
      invFun := fun f ↦ e.trans f
      left_inv := fun f ↦ Subtype.ext (Equiv.ext fun v ↦ by simp [Isomorphism.symm, Isomorphism.trans])
      right_inv := fun f ↦ Subtype.ext (Equiv.ext fun v ↦ by simp [Isomorphism.symm, Isomorphism.trans]) }
  exact Fintype.card_congr F

end RootedTree

namespace SignedNodeMatch

variable {T S : RootedTree}

noncomputable instance : Fintype (SignedNodeMatch T S) :=
  Fintype.ofInjective (fun M : SignedNodeMatch T S ↦ (M.node, M.orient)) (by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl)

/-- The number of signed permutations is bounded by the number of
unrestricted role and orientation choices. -/
theorem card_le (T S : RootedTree) :
    Fintype.card (SignedNodeMatch T S) ≤ (2 * T.nodeCount) ^ S.nodeCount := by
  let f (M : SignedNodeMatch T S) (v : S.Node) := (M.node v, M.orient v)
  have hInj : Function.Injective f := by
    intro a b hab
    have hn : a.node = b.node := Equiv.ext fun v ↦ congrArg Prod.fst (congrFun hab v)
    have ho : a.orient = b.orient := funext fun v ↦ congrArg Prod.snd (congrFun hab v)
    cases a
    cases b
    cases hn
    cases ho
    rfl
  simpa [Fintype.card_prod, mul_comm] using Fintype.card_le_of_injective f hInj

/-- An isomorphism with a choice of common orientation gives a
signed match. -/
def ofIsomorphism (e : S.Isomorphism T) (b : Bool) : SignedNodeMatch T S :=
  ⟨e.val, fun _ ↦ b⟩

private lemma children_map_isomorphism (e : S.Isomorphism T) (v : S.Node) :
    (S.children v).map e.val.toEmbedding = T.children (e.val v) := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hw
    obtain ⟨hne, hp⟩ := (S.mem_children_iff _ _).mp hu
    exact (T.mem_children_iff _ _).mpr ⟨e.val.injective.ne hne, (e.property.2 u).symm.trans
      (congrArg e.val hp)⟩
  · intro hw
    obtain ⟨hne, hp⟩ := (T.mem_children_iff _ _).mp hw
    let u := e.val.symm w
    have he : e.val u = w := e.val.apply_symm_apply w
    exact mem_map.mpr ⟨u, (S.mem_children_iff _ _).mpr
      ⟨fun hu ↦ hne (he.symm.trans (congrArg e.val hu)), e.val.injective
        ((e.property.2 u).trans (by rw [he, hp]))⟩, he⟩

lemma ofIsomorphism_preserves (e : S.Isomorphism T) (b : Bool) :
    (ofIsomorphism e b).PreservesParentSums := by
  intro v hv i
  have ht : (T.children (e.val v)).Nonempty :=
    (children_map_isomorphism e v) ▸ hv.map (f := e.val.toEmbedding)
  have he := congrFun (T.leafRow_eq_sum_children ht) i
  rw [Finset.sum_apply, ← children_map_isomorphism e, Finset.sum_map] at he
  have hReal (w : T.Node) : T.leafRow w i = (T.leafRowInt w i : ℝ) := by
    by_cases h : i ∈ T.descendantLeaves w <;> simp [RootedTree.leafRow, RootedTree.leafRowInt, h]
  simp_rw [hReal] at he
  have hInt : T.leafRowInt (e.val v) i = ∑ w ∈ S.children v, T.leafRowInt (e.val w) i := by
    exact_mod_cast he
  cases b <;> simp [parentRelation, row, ofIsomorphism, hInt, sum_neg_distrib]

/-- The root-preserving classification also includes the single-node tree. -/
lemma rootPreserving_parent_and_orientation_all (M : SignedNodeMatch T S)
    (h : M.PreservesParentSums) (hL : Fintype.card S.Leaf = Fintype.card T.Leaf)
    (hRoot : M.node S.root = T.root) :
    (∀ v, M.node (S.parent v) = T.parent (M.node v)) ∧
      ∀ v, M.orient v = M.orient S.root := by
  by_cases hT : 1 < T.nodeCount
  · exact M.rootPreserving_parent_and_orientation h hL hT hRoot
  have hEq : S.nodeCount = T.nodeCount := by
    simpa only [Fintype.card_fin] using Fintype.card_congr M.node
  have hv (v : S.Node) : v = S.root := by
    apply Fin.ext
    have h₁ := v.isLt
    have h₂ := S.root.isLt
    omega
  exact ⟨fun v ↦ by rw [hv v, S.parent_root, hRoot, T.parent_root], fun v ↦ by rw [hv v]⟩

/-- The root-to-root matches preserving all parent sums are the rooted
isomorphisms with a common orientation. -/
noncomputable def rootPreservingEquiv (hL : Fintype.card S.Leaf = Fintype.card T.Leaf) :
    {M : SignedNodeMatch T S // M.PreservesParentSums ∧ M.node S.root = T.root} ≃
      S.Isomorphism T × Bool where
  toFun M := (⟨M.val.node, M.property.2,
    (rootPreserving_parent_and_orientation_all M.val M.property.1 hL M.property.2).1⟩,
    M.val.orient S.root)
  invFun p := ⟨ofIsomorphism p.1 p.2, ofIsomorphism_preserves p.1 p.2, p.1.property.1⟩
  left_inv M := by
    have ho := (rootPreserving_parent_and_orientation_all M.val M.property.1 hL M.property.2).2
    apply Subtype.ext
    change ⟨M.val.node, fun _ ↦ M.val.orient S.root⟩ = M.val
    cases M with
    | mk M hM =>
      cases M
      congr 1
      exact (funext ho).symm
  right_inv := fun ⟨_, _⟩ ↦ rfl

end SignedNodeMatch

end LovaszTheta.Circulant
