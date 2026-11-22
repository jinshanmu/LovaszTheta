module

public import LovaszTheta.BranchingPopulation
public import LovaszTheta.GraftLeaves
public import LovaszTheta.PlaneTraversal
public import LovaszTheta.TreeFieldIsomorphism

/-!
# Unordered even-branching tree types

Ordered trees carry the branching weights. Forgetting the order
identifies finite rooted representatives up to rooted isomorphism.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace LovaszTheta.Circulant

namespace PlaneTree

/-- Every node has even outdegree. -/
def AllEven : PlaneTree → Prop
  | .mk j c => Even j ∧ ∀ i, AllEven (c i)

@[simp]
lemma allEven_mk (j : ℕ) (c : Fin j → PlaneTree) :
    AllEven (.mk j c) ↔ Even j ∧ ∀ i, AllEven (c i) := Iff.rfl

lemma weight_eq_zero_of_not_allEven (p : ℕ → ℝ≥0∞) (hp : ∀ j, Odd j → p j = 0)
    (t : PlaneTree) (ht : ¬t.AllEven) : weight p t = 0 := by
  induction t with
  | mk j c ih =>
    rw [weight_mk]
    by_cases hj : Even j
    · have h : ¬∀ i, AllEven (c i) := fun hall ↦ ht ⟨hj,hall⟩
      push Not at h
      obtain ⟨i,hi⟩ := h
      rw [prod_eq_zero (mem_univ i) (ih i hi), mul_zero]
    · rw [hp j (Nat.not_even_iff_odd.mp hj), zero_mul]

/-- Forget the plane order, retaining a finite ordinal vertex set. -/
noncomputable def rooted : (t : PlaneTree) → t.AllEven → RootedTree
  | .mk j c, h => RootedTree.graft (fun i : Fin j ↦ rooted (c i) (h.2 i))
      (by
        rw [Fintype.card_fin]
        obtain ⟨k,hk⟩ := h.1
        omega)

@[simp]
lemma rooted_nodeCount (t : PlaneTree) (h : t.AllEven) : (rooted t h).nodeCount = t.population := by
  induction t with
  | mk j c ih =>
    rw [population_mk, rooted, RootedTree.graft_nodeCount]
    simp only [ih]

end PlaneTree

/-- Plane trees of even outdegree at every vertex. -/
abbrev EvenPlaneTree := {t : PlaneTree // t.AllEven}

namespace EvenPlaneTree

/-- The rooted representative obtained by forgetting the order. -/
noncomputable def rooted (t : EvenPlaneTree) : RootedTree := t.val.rooted t.property

@[simp]
lemma rooted_nodeCount (t : EvenPlaneTree) : t.rooted.nodeCount = t.val.population :=
  PlaneTree.rooted_nodeCount _ _

/-- Orderings of the same rooted tree define the same type. -/
def typeSetoid : Setoid EvenPlaneTree where
  r s t := Nonempty (s.rooted.Isomorphism t.rooted)
  iseqv :=
    ⟨fun _ ↦ ⟨⟨Equiv.refl _,rfl,fun _ ↦ rfl⟩⟩,
     fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

end EvenPlaneTree

/-- Unordered finite tree types used as the indices of the Gaussians. -/
def EvenTreeType := Quotient EvenPlaneTree.typeSetoid

instance : Countable EvenTreeType := inferInstanceAs (Countable (Quotient EvenPlaneTree.typeSetoid))

namespace EvenTreeType

/-- The type of an ordered representative. -/
def ofPlane (t : EvenPlaneTree) : EvenTreeType := Quotient.mk EvenPlaneTree.typeSetoid t

lemma ofPlane_eq_iff (s t : EvenPlaneTree) :
    ofPlane s = ofPlane t ↔ Nonempty (s.rooted.Isomorphism t.rooted) :=
  @Quotient.eq _ EvenPlaneTree.typeSetoid s t

lemma ofPlane_out (T : EvenTreeType) : ofPlane (Quotient.out T) = T := Quotient.out_eq T

/-- The number of nodes, independent of any representative. -/
def nodeCount : EvenTreeType → ℕ :=
  Quotient.lift (fun t ↦ t.val.population) (fun s t ⟨e⟩ ↦ by
    simpa only [EvenPlaneTree.rooted_nodeCount] using e.nodeCount_eq)

@[simp]
lemma nodeCount_ofPlane (t : EvenPlaneTree) : (ofPlane t).nodeCount = t.val.population := rfl

/-- A representative of the type, used for evaluation on the signs. -/
noncomputable def representative (T : EvenTreeType) : RootedTree :=
  (Quotient.out T).rooted

lemma representative_nodeCount (T : EvenTreeType) :
    T.representative.nodeCount = T.nodeCount := by
  unfold representative
  rw [EvenPlaneTree.rooted_nodeCount, ← nodeCount_ofPlane, ofPlane_out]

lemma representative_isomorphism_iff (S T : EvenTreeType) :
    Nonempty (S.representative.Isomorphism T.representative) ↔ S = T := by
  rw [representative, representative, ← ofPlane_eq_iff, ofPlane_out, ofPlane_out]

/-- Plane representatives cover all the unordered types through the cutoff. -/
noncomputable def truncatedOfPlane (D : ℕ) (t : {t : EvenPlaneTree // t.val.population ≤ D}) :
    {T : EvenTreeType // T.nodeCount ≤ D} := ⟨ofPlane t.val,t.property⟩

lemma truncatedOfPlane_surjective (D : ℕ) : Function.Surjective (truncatedOfPlane D) := by
  rintro ⟨T,hT⟩
  exact ⟨⟨Quotient.out T,by rwa [← nodeCount_ofPlane, ofPlane_out]⟩,Subtype.ext (ofPlane_out T)⟩

/-- Forget the even outdegree constraint at a fixed size cutoff. -/
def evenPlaneEmbedding (D : ℕ) :
    {t : EvenPlaneTree // t.val.population ≤ D} ↪ {u : PlaneTree // u.population ≤ D} :=
  ⟨fun t ↦ ⟨t.val.val,t.property⟩, fun _ _ he ↦ by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {u : PlaneTree // u.population ≤ D} ↦ u.val) he⟩

noncomputable instance (D : ℕ) : Fintype {t : EvenPlaneTree // t.val.population ≤ D} :=
  Fintype.ofInjective _ (evenPlaneEmbedding D).injective

noncomputable instance (D : ℕ) : Fintype {T : EvenTreeType // T.nodeCount ≤ D} :=
  Fintype.ofSurjective _ (truncatedOfPlane_surjective D)

/-- At most four to the power of the cutoff unordered types occur. -/
theorem card_nodeCount_le (D : ℕ) : Fintype.card {T : EvenTreeType // T.nodeCount ≤ D} ≤ 4^D := by
  refine (Fintype.card_le_of_surjective _ (truncatedOfPlane_surjective D)).trans ?_
  exact (Fintype.card_le_of_injective _ (evenPlaneEmbedding D).injective).trans (PlaneTree.card_population_le D)

/-- The branching probability of an unordered type, summed over its
ordered representatives. -/
noncomputable def branchingProbability (p : ℕ → ℝ≥0∞) (T : EvenTreeType) : ℝ≥0∞ :=
  ∑' t : {t : EvenPlaneTree // ofPlane t = T}, PlaneTree.weight p t.val.val

/-- Summing a statistic over unordered types agrees with summing it
over ordered trees. Odd branching has weight zero. -/
theorem tsum_branchingProbability_mul (p : ℕ → ℝ≥0∞) (hp : ∀ j, Odd j → p j = 0)
    (f : ℕ → ℝ≥0∞) :
    (∑' T, branchingProbability p T * f T.nodeCount) =
      ∑' t : PlaneTree, PlaneTree.weight p t * f t.population := by
  let g (t : EvenPlaneTree) := PlaneTree.weight p t.val * f t.val.population
  calc
    _ = ∑' T : EvenTreeType, ∑' t : {t : EvenPlaneTree // ofPlane t = T}, g t.val := by
      apply tsum_congr
      intro T
      rw [branchingProbability, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro t
      change PlaneTree.weight p t.val.val * f T.nodeCount = PlaneTree.weight p t.val.val * f t.val.val.population
      rw [(congrArg nodeCount t.property).symm.trans (nodeCount_ofPlane t.val)]
    _ = ∑' t : EvenPlaneTree, g t := by
      rw [← tsum_sigma' (fun t : Σ T : EvenTreeType, {t : EvenPlaneTree // ofPlane t = T} ↦ g t.2.val)]
      exact (Equiv.sigmaFiberEquiv ofPlane).tsum_eq _
    _ = _ := by
      refine (_root_.tsum_subtype (Set.ofPred PlaneTree.AllEven)
        (fun t ↦ PlaneTree.weight p t * f t.population)).trans ?_
      apply tsum_congr
      intro t
      by_cases ht : t.AllEven
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, PlaneTree.weight_eq_zero_of_not_allEven p hp t ht, zero_mul]

/-- The Gaussian offspring law induces a probability on unordered
types and all population moments are finite. -/
theorem gaussian_branchingProbability_mass_and_moments {τ σ : ℝ}
    (hτ : 0 < τ) (hσ : 0 < σ) (hσ' : σ ≤ Real.sqrt (2*Real.pi))
    (hMean : activationMean τ σ = 2*Real.sqrt (1+τ)) :
    let p (j : ℕ) := ENNReal.ofReal (gaussianOffspringProbability τ σ j)
    (∑' T, branchingProbability p T) = 1 ∧
      ∀ r : ℕ, (∑' T, branchingProbability p T * (T.nodeCount : ℝ≥0∞)^r) ≠ ∞ := by
  let p (j : ℕ) := ENNReal.ofReal (gaussianOffspringProbability τ σ j)
  have hp (j : ℕ) (hj : Odd j) : p j = 0 := by
    simp [p, gaussianOffspringProbability_eq_zero_of_odd τ σ hj]
  obtain ⟨hMass,hm⟩ := PlaneTree.gaussian_weight_mass_and_population_moments hτ hσ hσ' hMean
  refine ⟨?_,fun r ↦ ?_⟩
  · have he := tsum_branchingProbability_mul p hp (fun _ ↦ 1)
    simp only [mul_one] at he
    exact he.trans hMass
  · rw [tsum_branchingProbability_mul p hp (fun d ↦ (d : ℝ≥0∞)^r)]
    exact hm r

end EvenTreeType

end LovaszTheta.Circulant
