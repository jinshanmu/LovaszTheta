module

public import LovaszTheta.TraceCodeWeights
public import Mathlib.Data.Finset.Powerset

/-!
# Counting codes of fixed defect

Each code uses one bit per position. The other data are a set of
marked records, one for each marked block. The number of records is
bounded by a fixed multiple of the defect.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Independent

variable {J V : Type*} [Fintype J] {α : J → BasicShape} {l v : ℕ}

/-- The bound on the number of marks per unit of defect. -/
def marksPerDefect (v : ℕ) : ℕ :=
  (1+2*(v+2))*(1+2*(v+2)^2+(2*(v+2)^2)^2)

/-- The base in the polynomial bound for marked records. -/
def traceCodeBase (l v : ℕ) : ℕ := (l+2)*(v+2)+1

/-- The exponent per unit of defect in the bound for codes. -/
def traceCodeExponent (v shapeCount : ℕ) : ℕ :=
  (1+shapeCount+(v+2)+1)*marksPerDefect v

/-- The code of the full trace word. -/
noncomputable def TraceWord.code (w : TraceWord α V l) (v : ℕ) :
    Fin (l+2) → TraceBlocks.StepCode l v :=
  fun i ↦ TraceBlocks.encodeStep w.blocks v i

private lemma sum_pow_le_add_one_pow (b r : ℕ) :
    (∑ k ∈ range (r+1), b^k) ≤ (b+1)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ',pow_succ' (b+1),add_mul,one_mul]
    simp_rw [pow_succ' b,← mul_sum,pow_zero]
    have h₁ : 1 ≤ (b+1)^r := Nat.one_le_pow _ _ (by omega)
    have h₂ := Nat.mul_le_mul_left b ih
    omega

private lemma card_small_subsets {D : Type*} [Fintype D] (r : ℕ) :
    ((univ : Finset D).powerset.filter fun s ↦ s.card ≤ r).card ≤ (Fintype.card D+1)^r := by
  let S := ((univ : Finset D).powerset.filter fun s ↦ s.card ≤ r)
  have hMaps (s : Finset D) (hs : s ∈ S) : s.card ∈ range (r+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hs).2)
  calc
    S.card = ∑ k ∈ range (r+1), (S.filter fun s ↦ s.card = k).card :=
      card_eq_sum_card_fiberwise hMaps
    _ ≤ ∑ k ∈ range (r+1), (Fintype.card D)^k := by
      apply sum_le_sum
      intro k _
      have hSub : S.filter (fun s ↦ s.card = k) ⊆ (univ : Finset D).powersetCard k := by
        intro s hs
        exact mem_powersetCard.mpr ⟨subset_univ _,(mem_filter.mp hs).2⟩
      refine (card_le_card hSub).trans ?_
      rw [card_powersetCard,card_univ]
      exact Nat.choose_le_pow _ _
    _ ≤ _ := sum_pow_le_add_one_pow _ _

private abbrev MarkedRecord (J : Type*) (l v : ℕ) :=
  Fin (l+2) × J × (Fin (v+2) → Option (TraceBlocks.Name l v))

private lemma card_records_add_one_le :
    Fintype.card (MarkedRecord J l v)+1 ≤ (traceCodeBase l v)^(1+Fintype.card J+(v+2)+1) := by
  let B := traceCodeBase l v
  have hL : l+2 ≤ B := by
    unfold B traceCodeBase
    have h := Nat.mul_le_mul_left (l+2) (show 1 ≤ v+2 by omega)
    rw [Nat.mul_one] at h
    omega
  have hB : 2 ≤ B := by omega
  have hTwo (n : ℕ) : n ≤ (2 : ℕ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have : 1 ≤ (2 : ℕ)^n := Nat.one_le_pow _ _ (by decide)
      omega
  have hJ : Fintype.card J ≤ B^(Fintype.card J) :=
    (hTwo _).trans (Nat.pow_le_pow_left hB _)
  have hD : Fintype.card (MarkedRecord J l v) ≤ B^(1+Fintype.card J+(v+2)) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Fintype.card_option]
    change (l+2)*(Fintype.card J*B^(v+2)) ≤ B^(1+Fintype.card J+(v+2))
    rw [pow_add B (1+Fintype.card J),pow_add B 1,pow_one,← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hL hJ)
  change Fintype.card (MarkedRecord J l v)+1 ≤ B^(1+Fintype.card J+(v+2)+1)
  rw [pow_succ]
  have h₂ := Nat.mul_le_mul_left (B^(1+Fintype.card J+(v+2))) hB
  have h₁ : 1 ≤ B^(1+Fintype.card J+(v+2)) := Nat.one_le_pow _ _ (by omega)
  omega

/-- The number of codes at defect `t` is at most one bit per block times the marked-record bound. -/
theorem card_codes_le {S : Type*} [Fintype S] (r : S → TraceWord α V l) (t : ℕ)
    (hv : ∀ j, (α j).additionalVertices ≤ v) (ht : ∀ s, (r s).blocks.defect = t) :
    (univ.image fun s ↦ (r s).code v).card ≤
      2^(l+2) * (traceCodeBase l v)^(traceCodeExponent v (Fintype.card J)*t) := by
  let D := MarkedRecord J l v
  let R := marksPerDefect v*t
  let codes := univ.image fun s ↦ (r s).code v
  let target := ((univ : Finset D).powerset.filter fun s ↦ s.card ≤ R).product
    (univ : Finset (Fin (l+2) → Bool))
  have hRepr (a : Fin (l+2) → TraceBlocks.StepCode l v) (ha : a ∈ codes) :
      ∃ s, (r s).code v = a := by
    obtain ⟨s,_,hs⟩ := mem_image.mp ha
    exact ⟨s,hs⟩
  let record (w : TraceWord α V l) (i : Fin (l+2)) : D :=
    (i,(w.val i).1,(w.code v i).reference)
  let describe (a : Fin (l+2) → TraceBlocks.StepCode l v) : Finset D × (Fin (l+2) → Bool) :=
    if ha : a ∈ codes then
      ((r (hRepr a ha).choose).blocks.markedPositions.image (record (r (hRepr a ha).choose)),
        fun i ↦ (a i).bit)
    else (∅,fun i ↦ (a i).bit)
  have hMaps : Set.MapsTo describe ↑codes ↑target := by
    intro a ha
    change a ∈ codes at ha
    unfold describe
    rw [dite_eq_left ha]
    refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),?_⟩,mem_univ _⟩
    let w := r (hRepr a ha).choose
    exact card_image_le.trans ((w.blocks.card_markedPositions_le w.repeated
      (fun i ↦ Nat.add_le_add_right (hv (w.val i).1) 2)).trans_eq
        (by rw [ht]; rfl))
  have hInj : Set.InjOn describe ↑codes := by
    intro a ha b hb h
    change a ∈ codes at ha
    change b ∈ codes at hb
    unfold describe at h
    rw [dite_eq_left ha,dite_eq_left hb] at h
    let w := r (hRepr a ha).choose
    let z := r (hRepr b hb).choose
    have hw : w.code v = a := (hRepr a ha).choose_spec
    have hz : z.code v = b := (hRepr b hb).choose_spec
    have hSets : w.blocks.markedPositions.image (record w) =
        z.blocks.markedPositions.image (record z) := congrArg Prod.fst h
    have hBit i : (a i).bit = (b i).bit := congrFun (congrArg Prod.snd h) i
    have hTransfer (x y : TraceWord α V l) (i : Fin (l+2))
        (hR : x.blocks.markedPositions.image (record x) =
          y.blocks.markedPositions.image (record y)) (hi : i ∈ x.blocks.markedPositions) :
        i ∈ y.blocks.markedPositions ∧ (x.val i).1 = (y.val i).1 ∧
          (x.code v i).reference = (y.code v i).reference := by
      have hm : record x i ∈ y.blocks.markedPositions.image (record y) :=
        hR ▸ mem_image.mpr ⟨i,hi,rfl⟩
      obtain ⟨j,hj,he⟩ := mem_image.mp hm
      have hij : j = i := congrArg Prod.fst he
      subst j
      exact ⟨hj,(congrArg (fun d : D ↦ d.2.1) he).symm,(congrArg (fun d : D ↦ d.2.2) he).symm⟩
    funext i
    have hEq (x y : TraceBlocks.StepCode l v)
        (he : x.markedShape = y.markedShape ∧ x.reference = y.reference ∧ x.bit = y.bit) : x = y := by
      rcases x with ⟨_,_,_⟩
      rcases y with ⟨_,_,_⟩
      obtain ⟨rfl,rfl,rfl⟩ := he
      rfl
    apply hEq
    refine ⟨?_,?_,hBit i⟩
    · rw [← hw,← hz]
      by_cases hi : i ∈ w.blocks.markedPositions
      · obtain ⟨hj,hj',_⟩ := hTransfer w z i hSets hi
        simp only [TraceWord.code,TraceBlocks.encodeStep,ite_eq_left hi,ite_eq_left hj,w.shape,z.shape,hj']
      · have hj : i ∉ z.blocks.markedPositions := fun hJ ↦ hi (hTransfer z w i hSets.symm hJ).1
        simp only [TraceWord.code,TraceBlocks.encodeStep,ite_eq_right hi,ite_eq_right hj]
    · rw [← hw,← hz]
      by_cases hi : i ∈ w.blocks.markedPositions
      · exact (hTransfer w z i hSets hi).2.2
      · have hj : i ∉ z.blocks.markedPositions := fun hJ ↦ hi (hTransfer z w i hSets.symm hJ).1
        simp only [TraceWord.code,TraceBlocks.encodeStep,ite_eq_right hi,ite_eq_right hj]
  calc
    codes.card ≤ target.card := card_le_card_of_injOn describe hMaps hInj
    _ = 2^(l+2)*((univ : Finset D).powerset.filter fun s ↦ s.card ≤ R).card := by
      have h := card_product ((univ : Finset D).powerset.filter fun s ↦ s.card ≤ R)
        (univ : Finset (Fin (l+2) → Bool))
      change target.card = _ at h
      rw [h,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]
    _ ≤ 2^(l+2)*(Fintype.card D+1)^R := Nat.mul_le_mul_left _ (card_small_subsets R)
    _ ≤ 2^(l+2)*(traceCodeBase l v)^(traceCodeExponent v (Fintype.card J)*t) := by
      apply Nat.mul_le_mul_left
      unfold traceCodeExponent
      rw [Nat.mul_assoc,pow_mul (traceCodeBase l v)]
      exact Nat.pow_le_pow_left (card_records_add_one_le (J := J) (l := l) (v := v)) R

end LovaszTheta.Independent
