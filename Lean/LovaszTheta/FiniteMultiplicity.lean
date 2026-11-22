module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Logic.Equiv.Sum

/-!
# Multiplicities in finite families

A multiset records a finite family's values and their
multiplicities. Equality of multisets is equivalent to a
value-preserving reindexing. The permutations preserving a
family permute its fibers independently.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace LovaszTheta.Circulant

/-- Record the values of a finite family with multiplicity. -/
noncomputable def familyMultiset {I A : Type*} [Fintype I] (f : I → A) : Multiset A :=
  (univ : Finset I).val.map f

lemma card_familyMultiset {I A : Type*} [Fintype I] (f : I → A) :
    (familyMultiset f).card = Fintype.card I := by simp [familyMultiset]

lemma count_familyMultiset {I A : Type*} [Fintype I] [DecidableEq A] (f : I → A) (a : A) :
    (familyMultiset f).count a = Fintype.card {i // f i = a} := by
  rw [familyMultiset, Multiset.count_map, Fintype.card_subtype, card_def, filter_val]
  have he := Multiset.filter_congr (s := (univ : Finset I).val)
    (p := fun i ↦ a = f i) (q := fun i ↦ f i = a) fun _ _ ↦ eq_comm
  rw [he]

lemma mem_familyMultiset_iff {I A : Type*} [Fintype I] (f : I → A) (a : A) :
    a ∈ familyMultiset f ↔ ∃ i, f i = a := by
  simp [familyMultiset, Multiset.mem_map]

variable {I J A : Type*} [Fintype I] [Fintype J]

/-- Equal multiplicities give a reindexing carrying each value to itself. -/
theorem familyMultiset_eq_iff (f : I → A) (g : J → A) :
    familyMultiset f = familyMultiset g ↔ ∃ e : I ≃ J, ∀ i, g (e i) = f i := by
  constructor
  · intro h
    let e (a : A) : {i // f i = a} ≃ {j // g j = a} :=
      (Fintype.card_eq.mp ((count_familyMultiset f a).symm.trans
        ((congrArg (Multiset.count a) h).trans (count_familyMultiset g a)))).some
    refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)),fun i ↦ ?_⟩
    exact (e (f i) ⟨i,rfl⟩).property
  · rintro ⟨e,he⟩
    apply Multiset.ext'
    intro a
    rw [count_familyMultiset,count_familyMultiset]
    exact Fintype.card_congr (e.subtypeEquiv (fun i ↦ by rw [he]))

/-- The successive values of a list, indexed by the finite ordinal
of its length, have the corresponding multiset. -/
theorem familyMultiset_get (l : List A) :
    familyMultiset (fun i : Fin l.length ↦ l[i]) = (l : Multiset A) := by
  apply Multiset.ext'
  intro a
  rw [count_familyMultiset, Multiset.coe_count]
  have h := List.count_ofFn (fun i : Fin l.length ↦ l[i]) a
  rw [Fintype.card_subtype]
  exact h.symm.trans (congrArg (List.count a) (List.ofFn_getElem (xs := l)))

/-- Permutations preserving the family's value at each position. -/
abbrev FamilyPerm (f : I → A) := {p : Equiv.Perm I // ∀ i, f (p i) = f i}

noncomputable instance (f : I → A) : Fintype (FamilyPerm f) := Fintype.ofFinite _

section

variable [DecidableEq A]

/-- The value at a position, considered in the support of the family. -/
noncomputable def familyValue (f : I → A) (i : I) : (familyMultiset f).toFinset :=
  ⟨f i, Multiset.mem_toFinset.mpr ((mem_familyMultiset_iff f (f i)).mpr ⟨i,rfl⟩)⟩

/-- The equivalence between positions and the fibers over the
finitely many values taken by the family. -/
noncomputable def familyFiberEquiv (f : I → A) :
    (Σ a : (familyMultiset f).toFinset, {i : I // f i = a.val}) ≃ I :=
  (Equiv.sigmaCongrRight (fun a ↦ (Equiv.refl I).subtypeEquiv (fun i ↦ by
    change f i = a.val ↔ familyValue f i = a
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩))).trans
      (Equiv.sigmaFiberEquiv (familyValue f))

/-- A value-preserving permutation is a family of permutations of
the individual fibers. -/
noncomputable def familyPermEquiv (f : I → A) :
    FamilyPerm f ≃ ∀ a : (familyMultiset f).toFinset, Equiv.Perm {i : I // f i = a.val} where
  toFun p a := p.val.subtypeEquiv (fun i ↦ by rw [p.property i])
  invFun q := ⟨(familyFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight q).trans (familyFiberEquiv f)),fun i ↦ by
      change f (q (familyValue f i) ⟨i,rfl⟩).val = f i
      exact (q (familyValue f i) ⟨i,rfl⟩).property⟩
  left_inv p := by
    apply Subtype.ext (Equiv.ext fun i ↦ ?_)
    rfl
  right_inv q := by
    funext a
    apply Equiv.ext
    rintro ⟨i,hi⟩
    have he : a = familyValue f i := Subtype.ext hi.symm
    subst a
    rfl

theorem card_familyPerm (f : I → A) :
    Fintype.card (FamilyPerm f) = ∏ a ∈ (familyMultiset f).toFinset, ((familyMultiset f).count a)! := by
  rw [Fintype.card_congr (familyPermEquiv f), Fintype.card_pi]
  simp only [Fintype.card_perm, count_familyMultiset]
  exact Finset.prod_coe_sort _ (fun a ↦ (Fintype.card {i // f i = a})!)

end

/-- The orderings of a fixed multiset on the same finite index set. -/
abbrev FamilyOrdering (f : I → A) := {g : I → A // familyMultiset g = familyMultiset f}

/-- Reindex a family by a permutation. -/
noncomputable def familyOrderingOfPerm (f : I → A) (p : Equiv.Perm I) : FamilyOrdering f :=
  ⟨f ∘ p.symm, ((familyMultiset_eq_iff f (f ∘ p.symm)).mpr
    ⟨p,fun i ↦ congrArg f (p.symm_apply_apply i)⟩).symm⟩

lemma familyOrderingOfPerm_surjective (f : I → A) : Function.Surjective (familyOrderingOfPerm f) := by
  intro g
  obtain ⟨p,hp⟩ := (familyMultiset_eq_iff f g.val).mp g.property.symm
  refine ⟨p, Subtype.ext (funext fun i ↦ ?_)⟩
  exact (hp (p.symm i)).symm.trans (congrArg g.val (p.apply_symm_apply i))

noncomputable instance (f : I → A) : Fintype (FamilyOrdering f) :=
  Fintype.ofSurjective _ (familyOrderingOfPerm_surjective f)

/-- A permutation has a specified ordering exactly when it
carries the value at every position to its prescribed destination. -/
lemma familyOrderingOfPerm_eq_iff (f : I → A) (g : FamilyOrdering f) (p : Equiv.Perm I) :
    familyOrderingOfPerm f p = g ↔ ∀ i, g.val (p i) = f i := by
  constructor
  · intro h i
    have he := congrFun (congrArg Subtype.val h) (p i)
    change f (p.symm (p i)) = g.val (p i) at he
    rwa [p.symm_apply_apply, eq_comm] at he
  · intro h
    exact Subtype.ext (funext fun i ↦ (h (p.symm i)).symm.trans (congrArg g.val (p.apply_symm_apply i)))

/-- Each ordering is attained by the same number of permutations,
given by independently permuting positions with identical values. -/
noncomputable def familyOrderingFiberEquiv (f : I → A) (g : FamilyOrdering f) :
    {p // familyOrderingOfPerm f p = g} ≃ FamilyPerm f := by
  let hex := (familyMultiset_eq_iff f g.val).mp g.property.symm
  let q := hex.choose
  have hq := hex.choose_spec
  refine
    { toFun := fun p ↦ ⟨p.val.trans q.symm,fun i ↦ by
        have h := (familyOrderingOfPerm_eq_iff f g p.val).mp p.property i
        exact (hq (q.symm (p.val i))).symm.trans ((congrArg g.val (q.apply_symm_apply _)).trans h)⟩
      invFun := fun p ↦ ⟨p.val.trans q,(familyOrderingOfPerm_eq_iff f g _).mpr fun i ↦
        (hq (p.val i)).trans (p.property i)⟩
      left_inv := fun p ↦ Subtype.ext (Equiv.ext fun i ↦ q.apply_symm_apply (p.val i))
      right_inv := fun p ↦ Subtype.ext (Equiv.ext fun i ↦ q.symm_apply_apply (p.val i)) }

/-- The multinomial count, written as a product to avoid division. -/
theorem card_familyOrdering_mul [DecidableEq A] (f : I → A) :
    Fintype.card (FamilyOrdering f) * (∏ a ∈ (familyMultiset f).toFinset, ((familyMultiset f).count a)!) =
      (Fintype.card I)! := by
  rw [← card_familyPerm f, ← Fintype.card_perm]
  let e : (FamilyOrdering f × FamilyPerm f) ≃ Equiv.Perm I :=
    (Equiv.sigmaEquivProd _ _).symm.trans
      ((Equiv.sigmaCongrRight fun g ↦ (familyOrderingFiberEquiv f g).symm).trans
        (Equiv.sigmaFiberEquiv (familyOrderingOfPerm f)))
  rw [← Fintype.card_congr e, Fintype.card_prod]

end LovaszTheta.Circulant
