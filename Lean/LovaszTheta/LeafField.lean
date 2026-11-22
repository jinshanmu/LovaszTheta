module

public import LovaszTheta.SignModes
public import LovaszTheta.TreeFields

/-!
# The one-node field

For the leaf the only residue is nonzero, and there is no
automorphism factor. The Fourier sum is the sign multiplier
applied to the origin atom, with the tree normalization.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LovaszTheta.Circulant.RootedTree

instance : Subsingleton single.Node := inferInstanceAs (Subsingleton (Fin 1))

/-- The distinguished leaf of the one-node tree. -/
def singleLeaf : single.Leaf :=
  ⟨single.root,fun _ _ ↦ Subsingleton.elim _ _⟩

instance : Unique single.Leaf where
  default := singleLeaf
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

instance : Unique single.Automorphism where
  default := ⟨Equiv.refl _,rfl,fun _ ↦ rfl⟩
  uniq _ := Subtype.ext (Equiv.ext fun _ ↦ Subsingleton.elim _ _)

lemma single_residue {n : ℕ} (a : single.Leaf → ZMod n) (u : single.Node) :
    single.residue a u = a singleLeaf := by
  rw [show u = singleLeaf.val from Subsingleton.elim _ _, residue_leaf]

/-- Admissible assignments on the one-node tree are nonzero residues. -/
def singleAssignmentEquiv (n : ℕ) : single.Assignment n ≃ {s : ZMod n // s ≠ 0} where
  toFun a := ⟨a.val singleLeaf,by simpa only [single_residue] using a.property.choose single.root⟩
  invFun s := ⟨fun _ ↦ s.val,⟨fun u ↦ by rw [single_residue]; exact s.property,fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩
  left_inv a := Subtype.ext (funext fun u ↦ congrArg a.val (Subsingleton.elim _ _))
  right_inv _ := rfl

/-- The leaf equals the normalized sign field at the Fourier origin. -/
theorem single_field_eq_signOperator {n : ℕ} [NeZero n] (x : InversionClass n → Bool) (k : ZMod n) :
    single.field x k = Real.sqrt n * signOperator x (Pi.single 0 1) k := by
  have hSq : (Real.sqrt n : ℂ) * (Real.sqrt n : ℂ) = (n : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hRoot : ((Real.sqrt n : ℝ) : ℂ) * (n : ℂ)⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hs : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
      intro he
      rw [he,zero_mul] at hSq
      exact hn' hSq.symm
    field_simp
    exact (pow_two _).trans hSq
  apply Complex.ofReal_injective
  rw [ofReal_field, Complex.ofReal_mul, signOperator_origin, ← mul_assoc, hRoot, fieldComplex]
  simp only [fieldNormalizer, Fintype.card_unique, pow_one, Nat.cast_one, Real.sqrt_one, mul_one, Complex.ofReal_inv]
  congr 1
  rw [← (singleAssignmentEquiv n).symm.sum_comp]
  have h (a : {s : ZMod n // s ≠ 0}) :
      ZMod.stdAddChar (-(single.residue ((singleAssignmentEquiv n).symm a).val single.root * k)) *
        (walsh (single.signSupport ((singleAssignmentEquiv n).symm a)) x : ℂ) =
      (epsilon x a.val : ℂ) * characterMode a.val k := by
    rw [single_residue, walsh_signSupport]
    change characterMode a.val k * ((∏ v : Fin 1, epsilon x (single.residue (fun _ ↦ a.val) v) : ℝ) : ℂ) = _
    have he (v : Fin 1) : single.residue (fun _ ↦ a.val) v = a.val := single_residue _ v
    simp [he,mul_comm]
  simp only [h]
  let f (s : ZMod n) := (epsilon x s : ℂ) * characterMode s k
  rw [← Finset.sum_subtype (univ.erase (0 : ZMod n)) (p := fun s ↦ s ≠ 0) (fun _ ↦ by simp) f]
  simp [f]

end LovaszTheta.Circulant.RootedTree
