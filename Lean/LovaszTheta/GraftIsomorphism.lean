module

public import LovaszTheta.GraftLeaves
public import LovaszTheta.RootMatchCounts

/-!
# Isomorphisms between grafts

A graft isomorphism permutes the child roots. Its restriction to
the descendants of each child root is a rooted isomorphism.
Conversely, those data extend over the new root.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

variable {I J : Type*} {S : I → RootedTree} {T : J → RootedTree} [Fintype I] [Fintype J]
  {hI : Fintype.card I ≠ 1} {hJ : Fintype.card J ≠ 1}

/-- Permuting and identifying the indexed children identifies the grafts. -/
noncomputable def graftIsomorphism (p : I ≃ J) (e : ∀ i, (S i).Isomorphism (T (p i))) :
    (graft S hI).Isomorphism (graft T hJ) := by
  let f : GraftNode S ≃ GraftNode T :=
    Equiv.optionCongr (Equiv.sigmaCongr p fun i ↦ (e i).val)
  refine ⟨(graftNodeEquiv S hI).symm.trans (f.trans (graftNodeEquiv T hJ)), ?_, ?_⟩
  · change graftNodeEquiv T hJ (f ((graftNodeEquiv S hI).symm (graftNodeEquiv S hI none))) =
      graftNodeEquiv T hJ none
    rw [Equiv.symm_apply_apply]
    rfl
  · intro v
    obtain ⟨u,rfl⟩ := (graftNodeEquiv S hI).surjective v
    change graftNodeEquiv T hJ (f ((graftNodeEquiv S hI).symm
      ((graft S hI).parent (graftNodeEquiv S hI u)))) =
      (graft T hJ).parent (graftNodeEquiv T hJ (f ((graftNodeEquiv S hI).symm (graftNodeEquiv S hI u))))
    simp only [graft_parent_nodeEquiv, Equiv.symm_apply_apply]
    congr 1
    rcases u with _ | ⟨i,w⟩
    · rfl
    · change f (graftParent S (some ⟨i,w⟩)) = graftParent T (some ⟨p i,(e i).val w⟩)
      by_cases hw : w = (S i).root
      · subst w
        rw [(e i).property.1]
        simp only [graftParent, ite_true]
        rfl
      · have hne : (e i).val w ≠ (T (p i)).root := fun he ↦ hw ((e i).val.injective (he.trans (e i).property.1.symm))
        simp only [graftParent, ite_eq_right hw, ite_eq_right hne]
        change (some ⟨p i,(e i).val ((S i).parent w)⟩ : GraftNode T) =
          some ⟨p i,(T (p i)).parent ((e i).val w)⟩
        rw [(e i).property.2]

lemma graftIsomorphism_apply_old (p : I ≃ J) (e : ∀ i, (S i).Isomorphism (T (p i)))
    (i : I) (v : (S i).Node) :
    (graftIsomorphism (hI := hI) (hJ := hJ) p e).val (graftEmbedding S hI i v) =
      graftEmbedding T hJ (p i) ((e i).val v) := by
  simp only [graftEmbedding_apply, graftIsomorphism, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

namespace Isomorphism

variable {A B : RootedTree}

/-- Isomorphisms transport the proper children bijectively. -/
noncomputable def childrenEquiv (e : A.Isomorphism B) (v : A.Node) :
    {u // u ∈ A.children v} ≃ {w // w ∈ B.children (e.val v)} :=
  e.val.subtypeEquiv (fun w ↦ by
    rw [A.mem_children_iff, B.mem_children_iff, ← e.property.2, e.val.injective.ne_iff, e.val.injective.eq_iff])

lemma isAncestor_iff (e : A.Isomorphism B) (u v : A.Node) :
    B.IsAncestor (e.val u) (e.val v) ↔ A.IsAncestor u v := by
  have h : Function.Semiconj e.val A.parent B.parent := e.property.2
  have he (k : ℕ) := h.iterate_right k v
  simp only [IsAncestor, ← he, e.val.injective.eq_iff]

/-- Isomorphisms carry the entire descendant set of a node to the
descendant set of its image. -/
noncomputable def descendantsEquiv (e : A.Isomorphism B) (v : A.Node) :
    {u // A.IsAncestor v u} ≃ {w // B.IsAncestor (e.val v) w} :=
  e.val.subtypeEquiv (fun _ ↦ (e.isAncestor_iff _ _).symm)

end Isomorphism

/-- The child index is equivalent to the vertex set of proper root children. -/
noncomputable def graftChildrenEquiv (S : I → RootedTree) (hI : Fintype.card I ≠ 1) :
    I ≃ {v // v ∈ (graft S hI).children (graft S hI).root} :=
  Equiv.ofBijective (fun i ↦ ⟨graftRootEmbedding S hI i, by rw [graft_children_root]; exact mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact (graftRootEmbedding S hI).injective (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      rw [graft_children_root] at hv
      obtain ⟨i,_,rfl⟩ := mem_map.mp hv
      exact ⟨i,rfl⟩)

/-- The induced permutation on the child set. -/
noncomputable def graftChildPerm (e : (graft S hI).Isomorphism (graft T hJ)) : I ≃ J :=
  (graftChildrenEquiv S hI).trans ((e.childrenEquiv (graft S hI).root).trans
    (((Equiv.refl (graft T hJ).Node).subtypeEquiv (fun w ↦ by
      change w ∈ (graft T hJ).children (e.val (graft S hI).root) ↔ w ∈ (graft T hJ).children (graft T hJ).root
      rw [e.property.1])).trans (graftChildrenEquiv T hJ).symm))

lemma graftChildPerm_root (e : (graft S hI).Isomorphism (graft T hJ)) (i : I) :
    graftRootEmbedding T hJ (graftChildPerm e i) = e.val (graftRootEmbedding S hI i) := by
  let w : {v // v ∈ (graft T hJ).children (graft T hJ).root} :=
    ⟨e.val (graftRootEmbedding S hI i), by
      have hw := (e.childrenEquiv _ (graftChildrenEquiv S hI i)).property
      change e.val (graftRootEmbedding S hI i) ∈ (graft T hJ).children (e.val (graft S hI).root) at hw
      simpa only [e.property.1] using hw⟩
  exact congrArg Subtype.val ((graftChildrenEquiv T hJ).apply_symm_apply w)

/-- A child is equivalent to all graft nodes below its root. -/
noncomputable def graftDescendantsEquiv (S : I → RootedTree) (hI : Fintype.card I ≠ 1) (i : I) :
    (S i).Node ≃ {v // (graft S hI).IsAncestor (graftRootEmbedding S hI i) v} :=
  Equiv.ofBijective (fun u ↦ ⟨graftEmbedding S hI i u,
    (graft_ancestor_old_iff S hI).mpr ⟨rfl,(S i).exists_iterate_parent_eq_root u⟩⟩) (by
    constructor
    · intro u v h
      exact (graftEmbedding S hI i).injective (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨w,rfl⟩ := (graftNodeEquiv S hI).surjective v
      rcases w with _ | ⟨j,w⟩
      · obtain ⟨k,hk⟩ := hv
        rw [graftNodeEquiv_none, Function.iterate_fixed (graft S hI).parent_root] at hk
        exact (graftEmbedding_ne_root S hI i (S i).root hk.symm).elim
      · obtain ⟨hji,_⟩ := (graft_ancestor_old_iff S hI (i := i) (j := j)).mp hv
        subst j
        exact ⟨w,rfl⟩)

/-- Restrict a graft isomorphism to the descendants of a child root. -/
noncomputable def graftRestricted (e : (graft S hI).Isomorphism (graft T hJ)) (i : I) :
    (S i).Node ≃ (T (graftChildPerm e i)).Node :=
  (graftDescendantsEquiv S hI i).trans
    ((e.descendantsEquiv (graftRootEmbedding S hI i)).trans
      (((Equiv.refl (graft T hJ).Node).subtypeEquiv (fun w ↦ by
        change (graft T hJ).IsAncestor (e.val (graftRootEmbedding S hI i)) w ↔
          (graft T hJ).IsAncestor (graftRootEmbedding T hJ (graftChildPerm e i)) w
        rw [graftChildPerm_root])).trans (graftDescendantsEquiv T hJ (graftChildPerm e i)).symm))

lemma graftRestricted_apply (e : (graft S hI).Isomorphism (graft T hJ)) (i : I) (u : (S i).Node) :
    graftEmbedding T hJ (graftChildPerm e i) (graftRestricted e i u) =
      e.val (graftEmbedding S hI i u) := by
  let w : {v // (graft T hJ).IsAncestor (graftRootEmbedding T hJ (graftChildPerm e i)) v} :=
    ⟨e.val (graftEmbedding S hI i u), by
      rw [graftChildPerm_root]
      exact (e.descendantsEquiv _ (graftDescendantsEquiv S hI i u)).property⟩
  exact congrArg Subtype.val ((graftDescendantsEquiv T hJ (graftChildPerm e i)).apply_symm_apply w)

/-- Each restriction preserves the child root and its parent map. -/
noncomputable def graftChildIso (e : (graft S hI).Isomorphism (graft T hJ)) (i : I) :
    (S i).Isomorphism (T (graftChildPerm e i)) := by
  let j := graftChildPerm e i
  have hRoot : graftRestricted e i (S i).root = (T j).root := by
    apply (graftEmbedding T hJ j).injective
    rw [graftRestricted_apply]
    exact (graftChildPerm_root e i).symm
  refine ⟨graftRestricted e i,hRoot,?_⟩
  intro u
  by_cases hu : u = (S i).root
  · rw [hu,(S i).parent_root,hRoot,(T j).parent_root]
  · have hv : graftRestricted e i u ≠ (T j).root := fun he ↦
      hu ((graftRestricted e i).injective (he.trans hRoot.symm))
    apply (graftEmbedding T hJ j).injective
    rw [graftRestricted_apply, ← graft_parent_old S hI i u hu, e.property.2,
      ← graftRestricted_apply, graft_parent_old T hJ j _ hv]

/-- A graft isomorphism is uniquely determined by the child
permutation and its restrictions to those children. -/
noncomputable def graftIsomorphismEquiv :
    (graft S hI).Isomorphism (graft T hJ) ≃ Σ p : I ≃ J, ∀ i, (S i).Isomorphism (T (p i)) where
  toFun e := ⟨graftChildPerm e, graftChildIso e⟩
  invFun p := graftIsomorphism p.1 p.2
  left_inv e := by
    apply Subtype.ext (Equiv.ext fun v ↦ ?_)
    obtain ⟨u,rfl⟩ := (graftNodeEquiv S hI).surjective v
    rcases u with _ | ⟨i,u⟩
    · rw [graftNodeEquiv_none]
      exact ((graftIsomorphism (graftChildPerm e) (graftChildIso e)).property.1).trans e.property.1.symm
    · exact (graftIsomorphism_apply_old (graftChildPerm e) (graftChildIso e) i u).trans
        (graftRestricted_apply e i u)
  right_inv := by
    rintro ⟨p,f⟩
    let e : (graft S hI).Isomorphism (graft T hJ) := graftIsomorphism p f
    have hp : graftChildPerm e = p := by
      apply Equiv.ext
      intro i
      apply (graftRootEmbedding T hJ).injective
      rw [graftChildPerm_root, graftRootEmbedding_apply, graftRootEmbedding_apply,
        graftIsomorphism_apply_old, (f i).property.1]
    change (⟨graftChildPerm e,graftChildIso e⟩ : Σ p : I ≃ J, ∀ i, (S i).Isomorphism (T (p i))) = ⟨p,f⟩
    apply Sigma.ext hp
    suffices ∀ (q : I ≃ J) (h : q = graftChildPerm e) (b : ∀ i, (S i).Isomorphism (T (q i))),
        (∀ i u, graftEmbedding T hJ (q i) ((b i).val u) = e.val (graftEmbedding S hI i u)) →
        HEq (graftChildIso e) b from this p hp.symm f (fun i u ↦ (graftIsomorphism_apply_old p f i u).symm)
    intro q h b hb
    subst q
    apply heq_of_eq
    funext i
    apply Subtype.ext (Equiv.ext fun u ↦ (graftEmbedding T hJ (graftChildPerm e i)).injective ?_)
    exact (graftRestricted_apply e i u).trans (hb i u).symm

end LovaszTheta.Circulant.RootedTree
