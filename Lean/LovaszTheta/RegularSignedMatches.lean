module

public import LovaszTheta.AdmissibleResidueCounts
public import LovaszTheta.RootMatchCounts

/-!
# Full-support matches away from singleton classes

The complete support determines the permutation of node roles.
Away from a self-opposite residue it also determines the sign at
each role.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.SignedNodeMatch

variable {T S : RootedTree} {n : ℕ}

lemma class_eq_of_matches (M : SignedNodeMatch T S) (a : T.Assignment n) (b : S.Assignment n)
    (h : M.Matches a.val b.val) (v : S.Node) :
    S.classEmbedding b v = T.classEmbedding a (M.node v) := by
  apply (inversionClass_eq_iff (b.property.choose v) (a.property.choose (M.node v))).mpr
  by_cases he : M.orient v
  · exact Or.inl (by simpa only [value, he, ite_true] using h v)
  · exact Or.inr (by simpa [value, he] using h v)

lemma signSupport_eq_of_matches (M : SignedNodeMatch T S) (a : T.Assignment n) (b : S.Assignment n)
    (h : M.Matches a.val b.val) : S.signSupport b = T.signSupport a := by
  ext c
  constructor
  · intro hc
    obtain ⟨v, _, hv⟩ := mem_map.mp hc
    exact mem_map.mpr ⟨M.node v, mem_univ _, (M.class_eq_of_matches a b h v).symm.trans hv⟩
  · intro hc
    obtain ⟨u, _, hu⟩ := mem_map.mp hc
    refine mem_map.mpr ⟨M.node.symm u, mem_univ _, ?_⟩
    rw [M.class_eq_of_matches a b h, M.node.apply_symm_apply]
    exact hu

/-- A signed match of a regular source assignment has a regular
target assignment. -/
theorem regularAssignment_of_matches (M : SignedNodeMatch T S)
    {a : T.Leaf → ZMod n} {b : S.Leaf → ZMod n} (ha : RegularAssignment T a)
    (h : M.Matches a b) : RegularAssignment S b := by
  have hb (v : S.Node) : S.residue b v + S.residue b v ≠ 0 := by
    rw [h v]
    by_cases hv : M.orient v
    · simpa only [value, hv, ite_true] using ha.2 (M.node v)
    · rw [value, ite_eq_right hv, ← neg_add]
      exact neg_ne_zero.mpr (ha.2 (M.node v))
  have hNz (v : S.Node) : S.residue b v ≠ 0 := fun he ↦ hb v (by simp [he])
  refine ⟨⟨hNz, ?_⟩, hb⟩
  have hC (v : S.Node) :
      inversionClass (S.residue b v) (hNz v) =
        inversionClass (T.residue a (M.node v)) (ha.1.choose (M.node v)) := by
    by_cases hv : M.orient v
    · exact (inversionClass_eq_iff _ _).mpr (Or.inl (by simpa [value, hv] using h v))
    · exact (inversionClass_eq_iff _ _).mpr (Or.inr (by simpa [value, hv] using h v))
  intro u v huv
  apply M.node.injective
  exact ha.1.choose_spec ((hC u).symm.trans (huv.trans (hC v)))

/-- Equal supports determine a unique signed permutation when the
source node residues are regular. -/
theorem existsUnique_of_equal_support (a : T.Assignment n) (b : S.Assignment n)
    (ha : RegularAssignment T a.val) (hI : S.signSupport b = T.signSupport a) :
    ∃! M : SignedNodeMatch T S, M.Matches a.val b.val := by
  have hEx (v : S.Node) : ∃ u : T.Node, T.classEmbedding a u = S.classEmbedding b v := by
    have hv : S.classEmbedding b v ∈ S.signSupport b := mem_map.mpr ⟨v, mem_univ _, rfl⟩
    rw [hI] at hv
    obtain ⟨u, _, he⟩ := mem_map.mp hv
    exact ⟨u, he⟩
  let node (v : S.Node) := (hEx v).choose
  have hClass (v : S.Node) : T.classEmbedding a (node v) = S.classEmbedding b v :=
    (hEx v).choose_spec
  have hInj : Function.Injective node := by
    intro u v he
    apply (S.classEmbedding b).injective
    rw [← hClass u, ← hClass v, he]
  have hSurj : Function.Surjective node := by
    intro u
    have hu : T.classEmbedding a u ∈ T.signSupport a := mem_map.mpr ⟨u, mem_univ _, rfl⟩
    rw [← hI] at hu
    obtain ⟨v, _, hv⟩ := mem_map.mp hu
    exact ⟨v, (T.classEmbedding a).injective ((hClass v).trans hv)⟩
  let e := Equiv.ofBijective node ⟨hInj, hSurj⟩
  let M : SignedNodeMatch T S := ⟨e, fun v ↦ decide (S.residue b.val v = T.residue a.val (node v))⟩
  have hM : M.Matches a.val b.val := by
    intro v
    have hEither := (inversionClass_eq_iff (b.property.choose v) (a.property.choose (node v))).mp
      (hClass v).symm
    change S.residue b.val v =
      if decide (S.residue b.val v = T.residue a.val (node v)) then T.residue a.val (node v)
      else -T.residue a.val (node v)
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact hEither.resolve_left h
  refine ⟨M, hM, ?_⟩
  intro N hN
  have hNode : N.node = M.node := Equiv.ext fun v ↦
    (T.classEmbedding a).injective ((N.class_eq_of_matches a b hN v).symm.trans
      (hClass v).symm)
  have hOrient : N.orient = M.orient := by
    funext v
    have hRes := hN v
    rw [SignedNodeMatch.value, hNode] at hRes
    change S.residue b.val v = if N.orient v then T.residue a.val (node v)
      else -T.residue a.val (node v) at hRes
    change N.orient v = decide (S.residue b.val v = T.residue a.val (node v))
    have hOpp : T.residue a.val (node v) ≠ -T.residue a.val (node v) :=
      fun he ↦ ha.2 _ (eq_neg_iff_add_eq_zero.mp he)
    cases ho : N.orient v
    · simp only [ho, Bool.false_eq_true, ite_false] at hRes
      have hNe : S.residue b.val v ≠ T.residue a.val (node v) := fun he ↦ hOpp (he.symm.trans hRes)
      simp [hNe]
    · simp only [ho, ite_true] at hRes
      simp [hRes]
  cases N
  dsimp only [M] at hNode hOrient ⊢
  subst_vars
  rfl

end LovaszTheta.Circulant.SignedNodeMatch
