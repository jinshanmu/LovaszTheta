module

public import LovaszTheta.ActivationProjection
public import LovaszTheta.HermiteGrafting

/-!
# Multiplicities in a finite Hermite projection

The projection expands into positive even multi-indices after its
constant term is removed. The multinomial theorem controls both
the number of these indices and their squared coefficient sum.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {I : Type*}

/-- The positive even Hermite indices supported in the cutoff. -/
noncomputable def finiteHermiteProducts (s : Finset I) (M : ℕ) :
    Finset (PositiveEvenHermiteIndex I) :=
  (((range (M+1)).filter (fun j ↦ 0 < j ∧ Even j)).biUnion (finsuppAntidiag s)).subtype
    (fun m ↦ 0 < m.toMultiset.card ∧ Even m.toMultiset.card)

private lemma card_toMultiset_eq_of_mem_antidiag {s : Finset I} {j : ℕ} {m : I →₀ ℕ}
    (hm : m ∈ finsuppAntidiag s j) : m.toMultiset.card = j :=
  (Finsupp.card_toMultiset _).trans (mem_finsuppAntidiag'.mp hm).1

lemma mem_finiteHermiteProducts {s : Finset I} {M : ℕ} {m : PositiveEvenHermiteIndex I} :
    m ∈ finiteHermiteProducts s M ↔ m.val.support ⊆ s ∧ m.val.toMultiset.card ≤ M := by
  unfold finiteHermiteProducts
  rw [mem_subtype,mem_biUnion]
  constructor
  · rintro ⟨j,hj,hm⟩
    refine ⟨(mem_finsuppAntidiag'.mp hm).2,?_⟩
    rw [card_toMultiset_eq_of_mem_antidiag hm]
    exact Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hj).1)
  · rintro ⟨hm,hd⟩
    exact ⟨m.val.toMultiset.card,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hd),m.property⟩,
      mem_finsuppAntidiag'.mpr ⟨(Finsupp.card_toMultiset _).symm,hm⟩⟩

private lemma sum_finsuppAntidiag_multinomial {R : Type*} [CommSemiring R]
    (s : Finset I) (u : I → R) (j : ℕ) :
    (∑ m ∈ finsuppAntidiag s j, (m.multinomial : R)*∏ i ∈ m.support, u i^(m i)) =
      (∑ i ∈ s, u i)^j := by
  rw [sum_pow_eq_sum_piAntidiag,finsuppAntidiag,sum_map]
  conv_rhs => rw [← sum_attach]
  refine sum_congr rfl fun m _ ↦ ?_
  let a : I →₀ ℕ := ⟨s.filter (fun i ↦ m.val i ≠ 0),m.val,by
    simpa using (mem_piAntidiag.mp m.property).2⟩
  change (a.multinomial : R)*(∏ i ∈ a.support, u i^(a i)) =
    (Nat.multinomial s a : R)*(∏ i ∈ s, u i^(a i))
  have ha : a.support ⊆ s := filter_subset _ _
  rw [a.multinomial_eq_of_support_subset ha]
  congr 1
  exact prod_subset ha (fun i _ hi ↦ by rw [Finsupp.notMem_support_iff.mp hi,pow_zero])

private lemma card_finsuppAntidiag_le (s : Finset I) (j : ℕ) :
    (finsuppAntidiag s j).card ≤ s.card^j := by
  calc
    _ = ∑ _ ∈ finsuppAntidiag s j, (1 : ℕ) := by simp
    _ ≤ ∑ m ∈ finsuppAntidiag s j, m.multinomial :=
      sum_le_sum fun (m : I →₀ ℕ) _ ↦ Nat.succ_le_of_lt (Nat.multinomial_pos (s := m.support) (f := m))
    _ = _ := by simpa using sum_finsuppAntidiag_multinomial s (fun _ ↦ (1 : ℕ)) j

private lemma sum_nat_pow_le (a M : ℕ) : (∑ j ∈ range (M+1), a^j) ≤ (a+1)^M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ,pow_succ (a+1)]
    have h : a^(M+1) ≤ (a+1)^M*a := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right a (Nat.pow_le_pow_left (Nat.le_succ a) _)
    exact (add_le_add ih h).trans_eq (by ring)

/-- There are at most `(s.card+1)^M` products in the finite projection. -/
theorem card_finiteHermiteProducts_le (s : Finset I) (M : ℕ) :
    (finiteHermiteProducts s M).card ≤ (s.card+1)^M := by
  unfold finiteHermiteProducts
  rw [card_subtype]
  refine (card_filter_le _ _).trans (card_biUnion_le.trans ?_)
  exact ((sum_le_sum fun j _ ↦ card_finsuppAntidiag_le s j).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _))).trans
      (sum_nat_pow_le s.card M)

lemma sum_finiteHermiteProducts {R : Type*} [AddCommMonoid R] (s : Finset I) (M : ℕ)
    (f : (I →₀ ℕ) → R) :
    (∑ m ∈ finiteHermiteProducts s M, f m.val) =
      ∑ j ∈ (range (M+1)).filter (fun j ↦ 0 < j ∧ Even j), ∑ m ∈ finsuppAntidiag s j, f m := by
  let J := (range (M+1)).filter (fun j ↦ 0 < j ∧ Even j)
  let F := J.biUnion (finsuppAntidiag s)
  have hF (m : I →₀ ℕ) (hm : m ∈ F) : 0 < m.toMultiset.card ∧ Even m.toMultiset.card := by
    obtain ⟨j,hj,hm⟩ := mem_biUnion.mp hm
    rw [card_toMultiset_eq_of_mem_antidiag hm]
    exact (mem_filter.mp hj).2
  have hDisj : (↑J : Set ℕ).PairwiseDisjoint (finsuppAntidiag s) := by
    rw [pairwiseDisjoint_iff]
    rintro i _ j _ ⟨m,hm⟩
    have h := mem_inter.mp hm
    exact (card_toMultiset_eq_of_mem_antidiag h.1).symm.trans (card_toMultiset_eq_of_mem_antidiag h.2)
  change (∑ m ∈ F.subtype _, f m.val) = _
  calc
    _ = ∑ m ∈ (F.subtype _).map (Function.Embedding.subtype _), f m :=
      (sum_map (F.subtype (fun m ↦ 0 < m.toMultiset.card ∧ Even m.toMultiset.card))
        (Function.Embedding.subtype _) f).symm
    _ = _ := by rw [subtype_map_of_mem hF,sum_biUnion hDisj]

/-- The coefficient in the projection of the activation in the finite Gaussian line. -/
noncomputable def activationHermiteProductCoeff (τ v : ℝ) (u : I → ℝ) (m : I →₀ ℕ) : ℝ :=
  activationCoefficient τ v m.toMultiset.card * hermiteLinearCoeff u m

/-- The sum of squares of the normalized Hermite product coefficients. -/
theorem sum_sq_activationHermiteProductCoeff_le {τ v : ℝ} (hτ : 0 ≤ τ)
    (s : Finset I) (M : ℕ) (u : I → ℝ) (hu : ∑ i ∈ s, u i^2 = 1) :
    (∑ m ∈ finiteHermiteProducts s M, activationHermiteProductCoeff τ v u m.val ^ 2) ≤ v^2+4*τ := by
  rw [sum_finiteHermiteProducts s M (fun m ↦ activationHermiteProductCoeff τ v u m ^ 2)]
  have h (j : ℕ) : (∑ m ∈ finsuppAntidiag s j, activationHermiteProductCoeff τ v u m ^ 2) =
      activationCoefficient τ v j ^ 2 := by
    calc
      _ = ∑ m ∈ finsuppAntidiag s j, activationCoefficient τ v j ^ 2 *
          ((m.multinomial : ℝ)*∏ i ∈ m.support, (u i^2)^(m i)) := by
        apply sum_congr rfl
        intro m hm
        rw [activationHermiteProductCoeff,card_toMultiset_eq_of_mem_antidiag hm,hermiteLinearCoeff,
          mul_pow,mul_pow,Real.sq_sqrt (by positivity),← prod_pow]
        simp only [← pow_mul,mul_comm 2]
      _ = _ := by rw [← mul_sum,sum_finsuppAntidiag_multinomial,hu,one_pow,mul_one]
  simp_rw [h]
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)).trans
    (sum_sq_activationCoefficient_le hτ v M)

/-- Expansion in finitely many Hermite products, with the constant coefficient displayed separately. -/
theorem activationProjection_eq_hermiteProducts {τ v : ℝ} (hv : v ≠ 0)
    (s : Finset I) (M : ℕ) (u x : I → ℝ) (hu : ∑ i ∈ s, u i^2 = 1) :
    activationProjection τ v M (v*(∑ i ∈ s, u i*x i)) =
      activationMean τ v + ∑ m ∈ finiteHermiteProducts s M,
        activationHermiteProductCoeff τ v u m.val * hermiteProduct m.val x := by
  let z := ∑ i ∈ s, u i*x i
  unfold activationProjection
  simp only [mul_div_cancel_left₀ _ hv]
  rw [sum_finiteHermiteProducts s M (fun m ↦ activationHermiteProductCoeff τ v u m*hermiteProduct m x)]
  have hTerm (j : ℕ) : (∑ m ∈ finsuppAntidiag s j,
      activationHermiteProductCoeff τ v u m * hermiteProduct m x) =
        activationCoefficient τ v j * normalizedHermite j z := by
    rw [normalizedHermite_linearCombination_finsupp s u x hu,mul_sum]
    exact sum_congr rfl fun m hm ↦ by
      rw [activationHermiteProductCoeff,card_toMultiset_eq_of_mem_antidiag hm,mul_assoc]
  simp_rw [hTerm, sum_filter]
  let f (j : ℕ) := activationCoefficient τ v j * normalizedHermite j z
  let g (j : ℕ) := if j = 0 then activationMean τ v else 0
  have hSplit (j : ℕ) : f j = g j + if 0 < j ∧ Even j then f j else 0 := by
    by_cases hj : j = 0
    · subst j
      simp [f,g,activationCoefficient_zero,normalizedHermite]
    · rw [show g j = 0 from ite_eq_right hj,zero_add]
      by_cases he : Even j
      · rw [ite_eq_left ⟨Nat.pos_of_ne_zero hj,he⟩]
      · rw [ite_eq_right (fun h ↦ he h.2)]
        simp only [f,activationCoefficient_eq_zero_of_odd τ v (Nat.not_even_iff_odd.mp he),zero_mul]
  change (∑ j ∈ range (M+1), f j) = activationMean τ v +
    ∑ j ∈ range (M+1), if 0 < j ∧ Even j then f j else 0
  rw [sum_congr rfl (fun j (_ : j ∈ range (M+1)) ↦ hSplit j),sum_add_distrib]
  congr 1
  simp [g]

end LovaszTheta.Circulant
