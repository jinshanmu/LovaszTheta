module

public import LovaszTheta.RandomGraphs
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Homogeneous sign degrees

The projection selects Walsh characters with a given support
size. In a sign product, even multiplicities cancel and any
repeated inversion class lowers the degree.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant

variable {C : Type*} [Fintype C]

/-- The Walsh coefficient of a real function on the sign cube. -/
noncomputable def walshCoefficient (f : (C → Bool) → ℝ) (s : Finset C) : ℝ :=
  average (fun x ↦ f x * walsh s x)

/-- Orthogonal projection onto terms of a prescribed sign degree. -/
noncomputable def walshDegree (d : ℕ) : ((C → Bool) → ℝ) →ₗ[ℝ] ((C → Bool) → ℝ) where
  toFun f := walshCombination (fun s ↦ if s.card = d then walshCoefficient f s else 0)
  map_add' f g := by
    funext x
    have he (s : Finset C) : walshCoefficient (f+g) s = walshCoefficient f s + walshCoefficient g s := by
      simp only [walshCoefficient,Pi.add_apply,add_mul,average_add]
    simp only [walshCombination,he,Pi.add_apply,← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by split_ifs <;> ring
  map_smul' c f := by
    funext x
    have he (s : Finset C) : walshCoefficient (c • f) s = c*walshCoefficient f s := by
      simp only [walshCoefficient,Pi.smul_apply,smul_eq_mul,mul_assoc,average_mul_left]
    simp only [RingHom.id_apply,walshCombination,he,Pi.smul_apply,smul_eq_mul,mul_sum]
    exact sum_congr rfl fun s _ ↦ by split_ifs <;> ring

lemma walshDegree_walsh (d : ℕ) (s : Finset C) :
    walshDegree d (walsh s) = if s.card = d then walsh s else 0 := by
  funext x
  change (∑ t : Finset C, (if t.card = d then average (fun y ↦ walsh s y*walsh t y) else 0) * walsh t x) = _
  simp only [average_walsh_mul]
  have he (t : Finset C) :
      (if t.card = d then if s = t then (1 : ℝ) else 0 else 0) * walsh t x =
        if s = t then ((if s.card = d then walsh s else 0) x) else 0 := by
    by_cases h : s = t
    · subst t
      by_cases hs : s.card = d <;> simp [hs]
    · simp [h]
  simp only [he,Finset.sum_ite_eq,mem_univ,ite_true]

lemma walshDegree_scalar_walsh (d : ℕ) (s : Finset C) (a : ℝ) :
    walshDegree d (fun x ↦ a*walsh s x) =
      if s.card = d then fun x ↦ a*walsh s x else 0 := by
  change walshDegree d (a • walsh s) = _
  rw [map_smul,walshDegree_walsh]
  split_ifs <;> first | rfl | simp

/-- The selected degree is orthogonal to the residual. -/
theorem average_sq_sub_walshDegree (d : ℕ) (f : (C → Bool) → ℝ) :
    average (fun x ↦ (f x - walshDegree d f x)^2) =
      average (fun x ↦ f x^2) - average (fun x ↦ (walshDegree d f x)^2) := by
  let h := walshDegree d f
  let a (s : Finset C) := if s.card = d then walshCoefficient f s else 0
  have hH : h = walshCombination a := rfl
  have h₀ : average (fun x ↦ h x^2) = ∑ s, a s^2 := by
    rw [hH]; simpa only [pow_two] using average_walshCombination_mul a a
  have h₁ : average (fun x ↦ f x*h x) = ∑ s, a s^2 := by
    simp only [hH,walshCombination,mul_sum,average_sum]
    apply sum_congr rfl
    intro s _
    have he (x : C → Bool) : f x*(a s*walsh s x) = a s*(f x*walsh s x) := by ring
    simp only [he,average_mul_left]
    change a s * walshCoefficient f s = _
    unfold a
    split_ifs <;> ring
  change average (fun x ↦ (f x-h x)^2) = average (fun x ↦ f x^2) - average (fun x ↦ h x^2)
  simp only [sub_pow_two,mul_assoc,average_add,average_sub,average_mul_left,h₀,h₁]
  ring

variable {V : Type*} [Fintype V]

/-- The sign indices with odd multiplicity among the vertices. -/
noncomputable def oddSignSupport (g : V → C) : Finset C :=
  univ.filter fun c ↦ Odd ((univ : Finset V).filter (fun v ↦ g v = c)).card

lemma prod_sign_eq_walsh_oddSignSupport (g : V → C) (x : C → Bool) :
    (∏ v, sign (x (g v))) = walsh (oddSignSupport g) x := by
  rw [← Finset.prod_fiberwise' (univ : Finset V) g (fun c ↦ sign (x c))]
  simp only [prod_const,walsh,oddSignSupport,prod_filter]
  apply prod_congr rfl
  intro c _
  generalize ((univ : Finset V).filter (fun v ↦ g v = c)).card = m
  by_cases h : Odd m
  · obtain ⟨k,rfl⟩ := h
    rw [ite_eq_left (show Odd (2*k+1) from ⟨k,rfl⟩),pow_succ, pow_mul, sign_sq,one_pow,one_mul]
  · obtain ⟨k,rfl⟩ := Nat.not_odd_iff_even.mp h
    rw [ite_eq_right h,← two_mul,pow_mul,sign_sq,one_pow]

lemma oddSignSupport_subset_image (g : V → C) : oddSignSupport g ⊆ (univ : Finset V).image g := by
  intro c hc
  simp only [oddSignSupport,mem_filter,mem_univ,true_and] at hc
  by_contra he
  have h : ((univ : Finset V).filter (fun v ↦ g v = c)) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro v hv
    exact he (mem_image.mpr ⟨v,mem_univ v,(mem_filter.mp hv).2⟩)
  rw [h,card_empty] at hc
  exact (by decide : ¬Odd (0 : ℕ)) hc

lemma card_oddSignSupport_le (g : V → C) : (oddSignSupport g).card ≤ Fintype.card V :=
  (card_le_card (oddSignSupport_subset_image g)).trans (card_image_le.trans_eq card_univ)

lemma card_oddSignSupport_lt_of_not_injective (g : V → C) (h : ¬Function.Injective g) :
    (oddSignSupport g).card < Fintype.card V := by
  refine (card_le_card (oddSignSupport_subset_image g)).trans_lt ?_
  rw [← card_univ]
  refine lt_of_le_of_ne card_image_le fun he ↦ h ?_
  exact fun a b hab ↦ (card_image_iff.mp he) (mem_univ a) (mem_univ b) hab

lemma oddSignSupport_eq_map (g : V ↪ C) : oddSignSupport g = univ.map g := by
  ext c
  constructor
  · intro hc
    obtain ⟨v,_,rfl⟩ := mem_image.mp (oddSignSupport_subset_image g hc)
    exact mem_map.mpr ⟨v,mem_univ v,rfl⟩
  · intro hc
    obtain ⟨v,_,rfl⟩ := mem_map.mp hc
    have he : (univ.filter fun w : V ↦ g w = g v) = {v} := by
      ext w
      simp [g.injective.eq_iff]
    simp only [oddSignSupport,mem_filter,mem_univ,true_and,he,card_singleton]
    decide

/-- The product of the signs at a finite family of residues. -/
noncomputable def residueSignProduct {n : ℕ} (r : V → ZMod n) (x : InversionClass n → Bool) : ℝ :=
  ∏ v, epsilon x (r v)

lemma residueSignProduct_eq_zero {n : ℕ} (r : V → ZMod n) (h : ∃ v, r v = 0) :
    residueSignProduct r = 0 := by
  obtain ⟨v,hv⟩ := h
  funext x
  exact prod_eq_zero (mem_univ v) (by rw [hv,epsilon_zero])

lemma residueSignProduct_eq_walsh {n : ℕ} [NeZero n] (r : V → ZMod n) (hr : ∀ v, r v ≠ 0) :
    residueSignProduct r = walsh (oddSignSupport (fun v ↦ inversionClass (r v) (hr v))) := by
  funext x
  change (∏ v, epsilon x (r v)) = _
  simp only [epsilon,dite_eq_right (hr _)]
  exact prod_sign_eq_walsh_oddSignSupport _ _

end LovaszTheta.Circulant
