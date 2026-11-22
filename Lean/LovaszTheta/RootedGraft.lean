module

public import LovaszTheta.TreeFields
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma

/-!
# Grafting a finite family of rooted trees

The nodes of a graft are its new root and the disjoint union of
the child nodes. Only the parent of each old root changes.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

/-- Present a rooted tree on a finite type as a tree indexed by a finite ordinal. -/
noncomputable def ofFinite {V : Type*} [Fintype V] (r : V) (p : V → V) (hr : p r = r)
    (dep : V → ℕ) (hd : ∀ v, v ≠ r → dep (p v) < dep v)
    (hn : ∀ v, ¬∃! u, u ≠ v ∧ p u = v) : RootedTree :=
  let e := Fintype.equivFin V
  { nodeCount := Fintype.card V
    root := e r
    parent := fun v ↦ e (p (e.symm v))
    parent_root := by rw [e.symm_apply_apply, hr]
    depth := fun v ↦ dep (e.symm v)
    depth_parent_lt := fun v hv ↦ by
      rw [e.symm_apply_apply]
      exact hd (e.symm v) (fun he ↦ hv (by rw [← he, e.apply_symm_apply]))
    noUnary := by
      intro v
      rintro ⟨u, hu, hu'⟩
      refine hn (e.symm v) ⟨e.symm u, ⟨e.symm.injective.ne hu.1, ?_⟩, ?_⟩
      · apply e.injective
        simpa only [e.apply_symm_apply] using hu.2
      · intro w hw
        apply e.injective
        rw [e.apply_symm_apply]
        exact hu' (e w) ⟨by
          intro he
          apply hw.1
          rw [← he, e.symm_apply_apply],
          by rw [e.symm_apply_apply, hw.2, e.apply_symm_apply]⟩ }

variable {I : Type*} (S : I → RootedTree)

/-- A graft node is either the newly added root or a node in an indexed child. -/
abbrev GraftNode := Option (Σ i, (S i).Node)

/-- The root of a child now has the new root as parent. -/
def graftParent : GraftNode S → GraftNode S
  | none => none
  | some ⟨i,u⟩ => if u = (S i).root then none else some ⟨i, (S i).parent u⟩

/-- Depth in a child is increased by one. -/
def graftDepth : GraftNode S → ℕ
  | none => 0
  | some ⟨i,u⟩ => (S i).depth u + 1

lemma graftDepth_parent_lt (v : GraftNode S) (hv : v ≠ none) :
    graftDepth S (graftParent S v) < graftDepth S v := by
  rcases v with _ | ⟨i,u⟩
  · exact (hv rfl).elim
  · by_cases hu : u = (S i).root
    · simp [graftParent, graftDepth, hu]
    · simp only [graftParent, ite_eq_right hu, graftDepth]
      exact Nat.succ_lt_succ ((S i).depth_parent_lt u hu)

/-- The proper children of the new root are exactly the old roots. -/
lemma graftProperChild_root_iff (w : GraftNode S) :
    w ≠ none ∧ graftParent S w = none ↔ ∃ i, w = some ⟨i, (S i).root⟩ := by
  constructor
  · rintro ⟨hne, hp⟩
    rcases w with _ | ⟨i,u⟩
    · exact (hne rfl).elim
    · use i
      have hu : u = (S i).root := by
        by_contra h
        simp [graftParent, h] at hp
      rw [hu]
  · rintro ⟨i,rfl⟩
    simp [graftParent]

/-- The proper children of an old node are unchanged by grafting. -/
lemma graftProperChild_some_iff (w : GraftNode S) (i : I) (v : (S i).Node) :
    w ≠ some ⟨i,v⟩ ∧ graftParent S w = some ⟨i,v⟩ ↔
      ∃ u : (S i).Node, u ≠ v ∧ (S i).parent u = v ∧ w = some ⟨i,u⟩ := by
  constructor
  · rintro ⟨hne, hp⟩
    rcases w with _ | ⟨j,u⟩
    · simp [graftParent] at hp
    · have hu : u ≠ (S j).root := by
        intro he
        simp [graftParent, he] at hp
      simp only [graftParent, ite_eq_right hu, Option.some.injEq] at hp
      have hji := congrArg Sigma.fst hp
      change j = i at hji
      subst j
      have he : (S i).parent u = v := eq_of_heq ((Sigma.mk.inj_iff.mp hp).2)
      exact ⟨u, fun h ↦ hne (by rw [h]), he, rfl⟩
  · rintro ⟨u, hne, hp, rfl⟩
    have hu : u ≠ (S i).root := by
      intro he
      apply hne
      rw [he, (S i).parent_root] at hp
      exact he.trans hp
    refine ⟨fun he ↦ hne (eq_of_heq ((Sigma.mk.inj_iff.mp (Option.some.inj he)).2)), ?_⟩
    simp [graftParent, hu, hp]

lemma graft_noUnary [Fintype I] (hI : Fintype.card I ≠ 1) (v : GraftNode S) :
    ¬∃! w, w ≠ v ∧ graftParent S w = v := by
  rintro ⟨w, hw, hUnique⟩
  rcases v with _ | ⟨i,v⟩
  · obtain ⟨i, hi⟩ := (graftProperChild_root_iff S w).mp hw
    have hAll (j : I) : j = i := by
      have h := hUnique (some ⟨j, (S j).root⟩)
        ((graftProperChild_root_iff S _).mpr ⟨j,rfl⟩)
      rw [hi] at h
      exact congrArg Sigma.fst (Option.some.inj h)
    let _ : Unique I := { default := i, uniq := hAll }
    exact hI Fintype.card_unique
  · obtain ⟨u, hu, hu', he⟩ := (graftProperChild_some_iff S w i v).mp hw
    apply (S i).noUnary v
    refine ⟨u, ⟨hu,hu'⟩, fun z hz ↦ ?_⟩
    have h := hUnique (some ⟨i,z⟩) ((graftProperChild_some_iff S _ i v).mpr ⟨z,hz.1,hz.2,rfl⟩)
    rw [he] at h
    exact eq_of_heq ((Sigma.mk.inj_iff.mp (Option.some.inj h)).2)

variable [Fintype I]

/-- Graft a new root above a family whose cardinality is different from one. -/
noncomputable def graft (hI : Fintype.card I ≠ 1) : RootedTree :=
  ofFinite (none : GraftNode S) (graftParent S) rfl (graftDepth S) (graftDepth_parent_lt S) (graft_noUnary S hI)

/-- The node equivalence used in the finite ordinal presentation. -/
noncomputable def graftNodeEquiv (hI : Fintype.card I ≠ 1) : GraftNode S ≃ (graft S hI).Node :=
  Fintype.equivFin (GraftNode S)

@[simp]
lemma graftNodeEquiv_none (hI : Fintype.card I ≠ 1) :
    graftNodeEquiv S hI none = (graft S hI).root := rfl

lemma graft_parent_nodeEquiv (hI : Fintype.card I ≠ 1) (v : GraftNode S) :
    (graft S hI).parent (graftNodeEquiv S hI v) = graftNodeEquiv S hI (graftParent S v) := by
  change graftNodeEquiv S hI (graftParent S ((graftNodeEquiv S hI).symm (graftNodeEquiv S hI v))) = _
  rw [Equiv.symm_apply_apply]

@[simp]
lemma graft_nodeCount (hI : Fintype.card I ≠ 1) :
    (graft S hI).nodeCount = 1+∑ i, (S i).nodeCount := by
  change Fintype.card (GraftNode S) = _
  rw [Fintype.card_option, Fintype.card_sigma, Nat.add_comm]
  simp only [Fintype.card_fin]

end LovaszTheta.Circulant.RootedTree
