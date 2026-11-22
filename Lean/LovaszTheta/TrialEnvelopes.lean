module

public import LovaszTheta.TrialEstimates

/-!
# Uniform growth of the finite-order envelopes

When both cutoffs equal D, each numerator in the finite estimates
is bounded by an exponential of a constant times `(D+1)^4`.
-/

@[expose] public section

namespace LovaszTheta.Circulant

/-- The common exponential bound for the errors at equal cutoffs. -/
def CutoffEnvelope (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℕ, 0 ≤ f D ∧ f D ≤ Real.exp (C * ((D : ℝ)+1)^4)

namespace CutoffEnvelope

private lemma scale_ge_one (D : ℕ) : (1 : ℝ) ≤ ((D : ℝ)+1)^4 :=
  one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) D])

private lemma self_le_exp (r : ℝ) : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]

lemma const {c : ℝ} (hc : 0 ≤ c) : CutoffEnvelope (fun _ ↦ c) :=
  ⟨c,hc,fun D ↦ ⟨hc,(self_le_exp _).trans (Real.exp_le_exp.mpr (le_mul_of_one_le_right hc (scale_ge_one D)))⟩⟩

lemma mul {f g : ℕ → ℝ} (hf : CutoffEnvelope f) (hg : CutoffEnvelope g) :
    CutoffEnvelope (fun D ↦ f D*g D) := by
  obtain ⟨a,ha,haf⟩ := hf
  obtain ⟨b,hb,hbg⟩ := hg
  refine ⟨a+b,by positivity,fun D ↦ ⟨mul_nonneg (haf D).1 (hbg D).1,?_⟩⟩
  rw [add_mul,Real.exp_add]
  exact mul_le_mul (haf D).2 (hbg D).2 (hbg D).1 (Real.exp_nonneg _)

lemma add {f g : ℕ → ℝ} (hf : CutoffEnvelope f) (hg : CutoffEnvelope g) :
    CutoffEnvelope (fun D ↦ f D+g D) := by
  obtain ⟨a,ha,haf⟩ := hf
  obtain ⟨b,hb,hbg⟩ := hg
  refine ⟨a+b+1,by positivity,fun D ↦ ⟨add_nonneg (haf D).1 (hbg D).1,?_⟩⟩
  let p := ((D : ℝ)+1)^4
  have hP : 0 ≤ p := by unfold p; positivity
  have h₁ : f D ≤ Real.exp ((a+b)*p) := (haf D).2.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb) hP))
  have h₂ : g D ≤ Real.exp ((a+b)*p) := (hbg D).2.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) hP))
  have hTwo : (2 : ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
  calc
    _ ≤ 2*Real.exp ((a+b)*p) := by linarith only [h₁,h₂]
    _ ≤ Real.exp p*Real.exp ((a+b)*p) := mul_le_mul_of_nonneg_right
      (hTwo.trans (Real.exp_le_exp.mpr (scale_ge_one D))) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; unfold p; congr 1; ring

private lemma pow_nat_le_exp (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    a^j ≤ Real.exp ((j : ℝ)*a) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ ha (self_le_exp _) _

private lemma pow_two_le_four (D : ℕ) : ((D : ℝ)+1)^2 ≤ ((D : ℝ)+1)^4 :=
  pow_right_mono₀ (by linarith [Nat.cast_nonneg (α := ℝ) D]) (by decide : (2 : ℕ) ≤ 4)

private lemma factorial (k : ℕ → ℕ) (hk : ∀ D : ℕ, (k D : ℝ) ≤ 2*((D : ℝ)+1)) :
    CutoffEnvelope (fun D ↦ ((k D).factorial : ℝ)) := by
  refine ⟨4,by norm_num,fun D ↦ ⟨by positivity,?_⟩⟩
  calc
    _ ≤ (k D : ℝ)^(k D) := by
      change ((k D).factorial : ℝ) ≤ (k D : ℝ)^(k D)
      exact_mod_cast Nat.factorial_le_pow (k D)
    _ ≤ Real.exp ((k D : ℝ)*(k D : ℝ)) := pow_nat_le_exp (k D : ℝ) (by positivity) _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ k D by positivity) (hk D) 2
      nlinarith only [h,pow_two_le_four D]

private lemma four_pow (k : ℕ → ℕ) (hk : ∀ D : ℕ, (k D : ℝ) ≤ ((D : ℝ)+1)^2) :
    CutoffEnvelope (fun D ↦ (4 : ℝ)^(k D)) :=
  ⟨4,by norm_num,fun D ↦ ⟨by positivity,(pow_nat_le_exp 4 (by norm_num) _).trans
    (Real.exp_le_exp.mpr (by linarith only [hk D,pow_two_le_four D]))⟩⟩

private lemma treeMoment (k : ℕ → ℕ) (hk : ∀ D : ℕ, (k D : ℝ) ≤ ((D : ℝ)+1)^2) :
    CutoffEnvelope (fun D ↦ treeMomentEnvelope (k D)) := by
  refine ⟨28,by norm_num,fun D ↦ ⟨by unfold treeMomentEnvelope; positivity,?_⟩⟩
  refine (treeMomentEnvelope_le_exp _).trans (Real.exp_le_exp.mpr ?_)
  have h := pow_le_pow_left₀ (show (0:ℝ) ≤ k D by positivity) (hk D) 2
  rw [← pow_mul] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

private lemma id_le_sq (D : ℕ) : (D : ℝ) ≤ ((D : ℝ)+1)^2 := by
  nlinarith only [sq_nonneg (D : ℝ),Nat.cast_nonneg (α := ℝ) D]

private lemma graftSize_le_sq (D : ℕ) : ((1+D*D : ℕ) : ℝ) ≤ ((D : ℝ)+1)^2 := by
  push_cast
  nlinarith only [Nat.cast_nonneg (α := ℝ) D]

lemma linearTransfer (k : ℕ → ℕ) (hk : ∀ D : ℕ, (k D : ℝ) ≤ ((D : ℝ)+1)^2) :
    CutoffEnvelope (fun D ↦ linearTransferScale (k D)) :=
  (four_pow k hk).mul (((const (by norm_num : (0 : ℝ) ≤ 3)).mul (treeMoment k hk)).add
    (const (by norm_num : (0 : ℝ) ≤ 2)))

lemma linearTransfer_size : CutoffEnvelope linearTransferScale := linearTransfer id id_le_sq

lemma linearTransfer_graft : CutoffEnvelope (fun D ↦ linearTransferScale (1+D*D)) :=
  linearTransfer _ graftSize_le_sq

lemma linearTransfer_zero :
    CutoffEnvelope (fun D ↦ (2*Real.pi)*((4 : ℝ)^D*treeMomentEnvelope D)) :=
  (const (by positivity)).mul ((four_pow id id_le_sq).mul (treeMoment id id_le_sq))

private lemma comparison {C : ℝ} (hC : 0 ≤ C) : CutoffEnvelope (fun D ↦ comparisonEnvelope C D D) := by
  refine ⟨3200*(C+1),by positivity,fun D ↦ ⟨by unfold comparisonEnvelope; positivity,?_⟩⟩
  unfold comparisonEnvelope
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_rfl

private lemma dimension : CutoffEnvelope (fun D ↦ ((4 : ℝ)^D+1)^D) := by
  refine ⟨5,by norm_num,fun D ↦ ⟨by positivity,?_⟩⟩
  have h := pow_nat_le_exp (4 : ℝ) (by norm_num) D
  have h₀ : 1 ≤ Real.exp ((D : ℝ)*4) := Real.one_le_exp (by positivity)
  have h₁ : (4 : ℝ)^D+1 ≤ Real.exp ((D : ℝ)*4+1) := by
    rw [Real.exp_add]
    have h₂ : (2 : ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    exact (show _ ≤ Real.exp ((D : ℝ)*4)*2 by linarith only [h,h₀]).trans
      (mul_le_mul_of_nonneg_left h₂ (Real.exp_nonneg _))
  refine (pow_le_pow_left₀ (by positivity) h₁ D).trans ?_
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith only [pow_two_le_four D,Nat.cast_nonneg (α := ℝ) D])

lemma grafting {τ : ℝ} (hτ : 0 ≤ τ) : CutoffEnvelope (fun D ↦ graftingTransferScale τ D D) := by
  have hQ : CutoffEnvelope (fun D ↦ EvenTreeType.graftProductErrorScale D D) :=
    (factorial (fun D ↦ 2*D) (fun D ↦ by push_cast; linarith)).mul (comparison (by norm_num))
  exact ((const (by positivity)).mul dimension).mul
    (((const (by norm_num : (0 : ℝ) ≤ 10)).mul hQ).add
      ((const (by norm_num : (0 : ℝ) ≤ 3)).mul (treeMoment _ graftSize_le_sq)) |>.add
        (const (by norm_num : (0 : ℝ) ≤ 4)))

private lemma activationMoment :
    CutoffEnvelope (fun D ↦
      let r : ℝ := 2*(D : ℝ)+3
      let u : ℝ := 2*Real.pi+4*(D : ℝ)
      Real.exp (6*r+3+r*(2*r*D+2*u+28*(D : ℝ)^2))) := by
  refine ⟨150+12*Real.pi,by positivity,fun D ↦ ⟨by positivity,?_⟩⟩
  let x := (D : ℝ)+1
  let r := 2*(D : ℝ)+3
  let u := 2*Real.pi+4*(D : ℝ)
  have hx₀ : 0 ≤ x := by unfold x; positivity
  have hD : (D : ℝ) ≤ x := by unfold x; linarith
  have hr : r ≤ 3*x := by unfold r x; linarith [Nat.cast_nonneg (α := ℝ) D]
  have hu : u ≤ 2*Real.pi+4*x := by unfold u; linarith only [hD]
  have hx : 1 ≤ x := by unfold x; linarith [Nat.cast_nonneg (α := ℝ) D]
  have hp (j : ℕ) (hj : j ≤ 4) : x^j ≤ x^4 := pow_right_mono₀ hx hj
  apply Real.exp_le_exp.mpr
  change 6*r+3+r*(2*r*D+2*u+28*(D : ℝ)^2) ≤ (150+12*Real.pi)*x^4
  calc
    _ ≤ 6*(3*x)+3+(3*x)*(2*(3*x)*x+2*(2*Real.pi+4*x)+28*x^2) := by
      have hr₀ : 0 ≤ r := by unfold r; positivity
      have hu₀ : 0 ≤ u := by unfold u; positivity
      gcongr
    _ ≤ _ := by
      have h₀ : (1 : ℝ) ≤ x^4 := (pow_zero x).symm.le.trans (hp 0 (by decide))
      have h₁ : x ≤ x^4 := (pow_one x).symm.le.trans (hp 1 (by decide))
      nlinarith only [h₀,h₁,hp 2 (by decide),hp 3 (by decide),
        mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 12*Real.pi by positivity)]

lemma activation {τ K : ℝ} (hK : 0 ≤ K) :
    CutoffEnvelope (fun D ↦ activationTransferScale τ K D D) := by
  have h₄ : CutoffEnvelope (fun D ↦ ((D : ℝ)+1)^4) :=
    ⟨1,by norm_num,fun D ↦ ⟨by positivity,by rw [one_mul]; exact self_le_exp _⟩⟩
  have hB := (((const (Real.sqrt_nonneg (2*Real.pi+4*τ))).mul h₄).mul
    (factorial id (fun D ↦ by change (D : ℝ) ≤ 2*((D : ℝ)+1); linarith [Nat.cast_nonneg (α := ℝ) D]))).add
      (const hK)
  unfold activationTransferScale
  simpa only [pow_two,id_eq] using (((const (by norm_num : (0 : ℝ) ≤ 8)).mul (hB.mul hB)).mul
    ((comparison (show 0 ≤ 2*Real.pi by positivity)).add
      ((const (by norm_num : (0 : ℝ) ≤ 2)).mul activationMoment)))

end CutoffEnvelope

end LovaszTheta.Circulant
