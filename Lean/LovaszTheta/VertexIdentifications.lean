module

public import LovaszTheta.ShapeIsomorphism

/-!
# Vertex identifications in matrix products

The identified vertices of the second factor are a partial injection
into the first factor. The quotient consists of the first factor and
the unmatched vertices of the second factor. A compatible pair of
labelings is the same as an identification and a labeling of that
quotient.
-/

@[expose] public section

open Finset Matrix
open scoped Classical symmDiff

namespace LovaszTheta.Independent

/-- A partial injection of the second vertex set into the first, including the joining pair. -/
abbrev Identification (P S : Shape) :=
  {f : Fin S.vertexCount → Option (Fin P.vertexCount) //
    f S.left = some P.right ∧ ∀ j k i, f j = some i → f k = some i → j = k}

namespace Identification

variable {P S : Shape} (p : Identification P S)

/-- The quotient vertex set of an identification. -/
abbrev Vertex (p : Identification P S) :=
  Fin P.vertexCount ⊕ {j : Fin S.vertexCount // p.val j = none}

/-- The inclusion of the old factor into the quotient. -/
def old : Fin P.vertexCount ↪ p.Vertex := Function.Embedding.inl

/-- The quotient vertex represented by one vertex of the multiplying factor. -/
def newVertex (j : Fin S.vertexCount) : p.Vertex :=
  if h : p.val j = none then .inr ⟨j,h⟩
  else .inl ((p.val j).get (Option.isSome_iff_ne_none.mpr h))

lemma newVertex_of_some {j : Fin S.vertexCount} {i : Fin P.vertexCount} (h : p.val j = some i) :
    p.newVertex j = p.old i := by
  unfold newVertex
  rw [dite_eq_right (fun hn ↦ Option.some_ne_none i (h.symm.trans hn))]
  exact congrArg Sum.inl (Option.get_of_eq_some _ h)

lemma newVertex_of_none {j : Fin S.vertexCount} (h : p.val j = none) :
    p.newVertex j = .inr ⟨j,h⟩ := by simp [newVertex,h]

/-- The inclusion of the multiplying factor into the quotient. -/
def new : Fin S.vertexCount ↪ p.Vertex where
  toFun := p.newVertex
  inj' := by
    intro j k h
    change p.newVertex j = p.newVertex k at h
    cases hj : p.val j with
    | none =>
      rw [p.newVertex_of_none hj] at h
      cases hk : p.val k with
      | none =>
        rw [p.newVertex_of_none hk] at h
        exact congrArg Subtype.val (Sum.inr.inj h)
      | some i =>
        rw [p.newVertex_of_some hk] at h
        cases h
    | some i =>
      rw [p.newVertex_of_some hj] at h
      cases hk : p.val k with
      | none =>
        rw [p.newVertex_of_none hk] at h
        cases h
      | some a =>
        rw [p.newVertex_of_some hk] at h
        exact p.property.2 j k i hj ((p.old.injective h).symm ▸ hk)

lemma new_of_some {j : Fin S.vertexCount} {i : Fin P.vertexCount} (h : p.val j = some i) :
    p.new j = p.old i := p.newVertex_of_some h

lemma new_of_none {j : Fin S.vertexCount} (h : p.val j = none) :
    p.new j = .inr ⟨j,h⟩ := p.newVertex_of_none h

lemma overlap_iff {j : Fin S.vertexCount} {i : Fin P.vertexCount} :
    p.new j = p.old i ↔ p.val j = some i := by
  constructor
  · intro h
    cases he : p.val j with
    | none =>
      rw [p.new_of_none he] at h
      cases h
    | some a =>
      rw [p.new_of_some he] at h
      rw [p.old.injective h]
  · exact p.new_of_some

@[simp]
lemma join : p.new S.left = p.old P.right := p.new_of_some p.property.1

/-- The vertices identified with some vertex of the old factor. -/
noncomputable def shared : Finset p.Vertex :=
  univ.filter (fun u ↦ u ∈ Set.range p.old ∧ u ∈ Set.range p.new)

lemma mem_shared {u : p.Vertex} : u ∈ p.shared ↔ u ∈ Set.range p.old ∧ u ∈ Set.range p.new := by
  simp [shared]

lemma vertex_in_factors (u : p.Vertex) : u ∈ Set.range p.old ∨ u ∈ Set.range p.new := by
  cases u with
  | inl i => exact Or.inl ⟨i,rfl⟩
  | inr j => exact Or.inr ⟨j.val,p.new_of_none j.property⟩

lemma card_vertex_add_shared :
    Fintype.card p.Vertex + p.shared.card = P.vertexCount + S.vertexCount := by
  let A := (univ : Finset (Fin P.vertexCount)).map p.old
  let B := (univ : Finset (Fin S.vertexCount)).map p.new
  have hU : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro u
    rcases p.vertex_in_factors u with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact mem_union_left _ (mem_map.mpr ⟨i,mem_univ _,hi⟩)
    · exact mem_union_right _ (mem_map.mpr ⟨j,mem_univ _,hj⟩)
  have hI : A ∩ B = p.shared := by
    ext u
    simp [A,B,mem_shared]
  simpa only [hU,hI,A,B,card_map,card_univ,Fintype.card_fin] using card_union_add_card_inter A B

/-- The old graph on the quotient. -/
def oldGraph : SimpleGraph p.Vertex := P.graph.map p.old

/-- The multiplying graph on the quotient. -/
def newGraph : SimpleGraph p.Vertex := S.graph.map p.new

/-- The remaining graph after canceling edges in both factors. -/
def remaining : SimpleGraph p.Vertex :=
  (p.oldGraph \ p.newGraph) ⊔ (p.newGraph \ p.oldGraph)

/-- The quotient graph, numbered by an enumeration of the quotient vertex set. -/
noncomputable def shape : Shape := by
  let e := Fintype.equivFin p.Vertex
  exact ⟨Fintype.card p.Vertex,p.remaining.comap e.symm,e (p.old P.left),e (p.new S.right)⟩

/-- Pairs of labelings that agree on the joining vertex. -/
abbrev Compatible (P S : Shape) (V : Type*) :=
  {fg : (Fin P.vertexCount ↪ V) × (Fin S.vertexCount ↪ V) // fg.1 P.right = fg.2 S.left}

variable {V : Type*}

/-- The old vertex carrying a given label, when that label is present. -/
noncomputable def findOld (f : Fin P.vertexCount ↪ V) (u : V) :
    Option (Fin P.vertexCount) :=
  if h : ∃ i, f i = u then some h.choose else none

lemma findOld_eq_some {f : Fin P.vertexCount ↪ V} {u : V} {i : Fin P.vertexCount} :
    findOld f u = some i ↔ f i = u := by
  by_cases h : ∃ j, f j = u
  · rw [findOld,dite_eq_left h,Option.some.injEq]
    exact ⟨fun he ↦ he ▸ h.choose_spec,fun he ↦ f.injective (h.choose_spec.trans he.symm)⟩
  · rw [findOld,dite_eq_right h]
    exact iff_of_false (by simp) (fun he ↦ h ⟨i,he⟩)

lemma findOld_eq_none {f : Fin P.vertexCount ↪ V} {u : V} :
    findOld f u = none ↔ ∀ i, f i ≠ u := by
  unfold findOld
  by_cases h : ∃ j, f j = u
  · rw [dite_eq_left h]
    exact iff_of_false (Option.some_ne_none _) (fun hn ↦ hn h.choose h.choose_spec)
  · rw [dite_eq_right h]
    exact iff_of_true rfl (fun i hi ↦ h ⟨i,hi⟩)

/-- The identifications induced by two compatible labelings. -/
noncomputable def ofLabelings (fg : Compatible P S V) : Identification P S :=
  ⟨fun j ↦ findOld fg.val.1 (fg.val.2 j),
    findOld_eq_some.mpr fg.property,
    fun _ _ _ h₁ h₂ ↦ fg.val.2.injective
      ((findOld_eq_some.mp h₁).symm.trans (findOld_eq_some.mp h₂))⟩

@[simp]
lemma ofLabelings_overlap {fg : Compatible P S V} {i : Fin P.vertexCount} {j : Fin S.vertexCount} :
    (ofLabelings fg).val j = some i ↔ fg.val.1 i = fg.val.2 j := findOld_eq_some

/-- The induced labeling of the quotient. -/
noncomputable def quotientLabeling (fg : Compatible P S V) : (ofLabelings fg).Vertex ↪ V where
  toFun := Sum.elim fg.val.1 (fg.val.2 ∘ Subtype.val)
  inj' := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (fg.val.1.injective h)
      | inr j => exact (findOld_eq_none.mp j.property i h).elim
    | inr i =>
      cases v with
      | inl j => exact (findOld_eq_none.mp i.property j h.symm).elim
      | inr j => exact congrArg Sum.inr (Subtype.ext (fg.val.2.injective h))

lemma quotientLabeling_old (fg : Compatible P S V) (i : Fin P.vertexCount) :
    quotientLabeling fg ((ofLabelings fg).old i) = fg.val.1 i := rfl

lemma quotientLabeling_new (fg : Compatible P S V) (j : Fin S.vertexCount) :
    quotientLabeling fg ((ofLabelings fg).new j) = fg.val.2 j := by
  cases he : (ofLabelings fg).val j with
  | none => rw [(ofLabelings fg).new_of_none he]; rfl
  | some i =>
    rw [(ofLabelings fg).new_of_some he,quotientLabeling_old]
    exact findOld_eq_some.mp he

/-- Restricting a quotient labeling to the two factors. -/
def restrict (f : p.Vertex ↪ V) : Compatible P S V :=
  ⟨(p.old.trans f,p.new.trans f),congrArg f p.join.symm⟩

lemma ofLabelings_restrict (f : p.Vertex ↪ V) : ofLabelings (p.restrict f) = p := by
  apply Subtype.ext
  funext j
  cases he : p.val j with
  | some i =>
    exact findOld_eq_some.mpr (congrArg f (p.new_of_some he).symm)
  | none =>
    apply findOld_eq_none.mpr
    intro i hi
    have h : p.old i = p.new j := f.injective hi
    rw [p.new_of_none he] at h
    cases h

lemma embedding_heq_of_same_restrictions {p q : Identification P S}
    (he : q = p) (f : p.Vertex ↪ V) (g : q.Vertex ↪ V)
    (hOld : ∀ i, g (q.old i) = f (p.old i)) (hNew : ∀ j, g (q.new j) = f (p.new j)) :
    HEq g f := by
  subst q
  apply heq_of_eq
  ext u
  rcases p.vertex_in_factors u with ⟨i,rfl⟩ | ⟨j,rfl⟩
  · exact hOld i
  · exact hNew j

/-- The bijection between compatible labelings and labeled identifications. -/
noncomputable def labelingEquiv (P S : Shape) (V : Type*) :
    Compatible P S V ≃ (Σ p : Identification P S, p.Vertex ↪ V) where
  toFun fg := ⟨ofLabelings fg,quotientLabeling fg⟩
  invFun x := x.1.restrict x.2
  left_inv fg := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      exact quotientLabeling_old fg i
    · ext j
      exact quotientLabeling_new fg j
  right_inv := by
    rintro ⟨p,f⟩
    apply Sigma.ext (ofLabelings_restrict p f)
    exact embedding_heq_of_same_restrictions (ofLabelings_restrict p f) f _
      (quotientLabeling_old (p.restrict f)) (quotientLabeling_new (p.restrict f))

end Identification

end LovaszTheta.Independent
