import LeanResearch.RepulsiveCoulomb.JordanPhysicalHalfplane
import LeanResearch.RepulsiveCoulomb.JordanAffineTraceTangent
import LeanResearch.RepulsiveCoulomb.JordanRoundedPointIncrement
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.Linarith

/-! Exact physical tangent transport across a small C1 replacement. All
hypotheses concern actual traces, derivatives and positive physical projections;
none asserts a turning or winding identity. Records-only, uncompiled. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem physical_deriv_eq_of_eqOn_Icc {f g : ℝ → ℂ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) (heq : EqOn f g (Icc a b)) :
    deriv f t = deriv g t := by
  have hud := uniqueDiffOn_Icc hab t ht
  calc
    deriv f t = derivWithin f (Icc a b) t :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin hud).symm
    _ = derivWithin g (Icc a b) t := derivWithin_congr heq (heq ht)
    _ = deriv g t := hg.hasDerivAt.hasDerivWithinAt.derivWithin hud

/-- Four arbitrary arc lifts are compared with one physical half-plane
branch. Exact attachment jets and the new common midpoint jet telescope. -/
theorem physical_corner_rounding_tangent_accounting
    (L R A B : ℝ → ℂ)
    (hL : ContDiff ℝ 1 L) (hR : ContDiff ℝ 1 R)
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (a b : Icc (0 : ℝ) 1) (c : ℂ)
    (hLp : ∀ t : Icc (0 : ℝ) 1,
      deriv L (unitIntervalAffine b 1 t) ∈ physicalHalfplane c)
    (hRp : ∀ t : Icc (0 : ℝ) 1,
      deriv R (unitIntervalAffine 0 a t) ∈ physicalHalfplane c)
    (hAp : ∀ t : Icc (0 : ℝ) 1,
      deriv A (unitIntervalAffine b 1 t) ∈ physicalHalfplane c)
    (hBp : ∀ t : Icc (0 : ℝ) 1,
      deriv B (unitIntervalAffine 0 a t) ∈ physicalHalfplane c)
    (hcutL : deriv A b = deriv L b) (hcutR : deriv B a = deriv R a)
    (hseam : deriv A 1 = deriv B 0)
    (hc : deriv R 0 / deriv L 1 ∈ Complex.slitPlane)
    (θL θR ψL ψR : Icc (0 : ℝ) 1 → ℝ)
    (hθL : Continuous θL) (hθR : Continuous θR)
    (hψL : Continuous ψL) (hψR : Continuous ψR)
    (hθLl : ∀ t, Complex.exp ((θL t : ℂ) * Complex.I) = deriv L t / (‖deriv L t‖ : ℂ))
    (hθRl : ∀ t, Complex.exp ((θR t : ℂ) * Complex.I) = deriv R t / (‖deriv R t‖ : ℂ))
    (hψLl : ∀ t, Complex.exp ((ψL t : ℂ) * Complex.I) = deriv A t / (‖deriv A t‖ : ℂ))
    (hψRl : ∀ t, Complex.exp ((ψR t : ℂ) * Complex.I) = deriv B t / (‖deriv B t‖ : ℂ)) :
    (ψL 1 - ψL b) + (ψR a - ψR 0) =
      (θL 1 - θL b) + (θR a - θR 0) + Complex.arg (deriv R 0 / deriv L 1) := by
  have hcont (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g) (a b : Icc (0 : ℝ) 1) :
      Continuous (fun t : Icc (0 : ℝ) 1 => deriv g (unitIntervalAffine a b t)) :=
    (hg.continuous_deriv_one.comp continuous_subtype_val).comp (unitIntervalAffine_continuous a b)
  have h₁ := physicalHalfplane_lift_increment (hcont L hL b 1) hLp
    (hθL.comp (unitIntervalAffine_continuous b 1))
    (fun t => hθLl (unitIntervalAffine b 1 t)) (0 : Icc (0 : ℝ) 1) 1
  have h₂ := physicalHalfplane_lift_increment (hcont R hR 0 a) hRp
    (hθR.comp (unitIntervalAffine_continuous 0 a))
    (fun t => hθRl (unitIntervalAffine 0 a t)) (0 : Icc (0 : ℝ) 1) 1
  have h₃ := physicalHalfplane_lift_increment (hcont A hA b 1) hAp
    (hψL.comp (unitIntervalAffine_continuous b 1))
    (fun t => hψLl (unitIntervalAffine b 1 t)) (0 : Icc (0 : ℝ) 1) 1
  have h₄ := physicalHalfplane_lift_increment (hcont B hB 0 a) hBp
    (hψR.comp (unitIntervalAffine_continuous 0 a))
    (fun t => hψRl (unitIntervalAffine 0 a t)) (0 : Icc (0 : ℝ) 1) 1
  simp only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one, Set.Icc.coe_zero, Set.Icc.coe_one] at h₁ h₂ h₃ h₄
  have hcorner := physicalHalfplaneArg_corner
    (by simpa only [unitIntervalAffine_one, Set.Icc.coe_one] using hLp 1)
    (by simpa only [unitIntervalAffine_zero, Set.Icc.coe_zero] using hRp 0) hc
  rw [hcutL, hseam] at h₃
  rw [hcutR] at h₄
  linarith

/-- Finite full turn transport from actual local half-plane data. The rounded
family, geometric windows, and positive projections will be constructed by the
physical rounding theorem; no local or global turn identity is assumed here. -/
theorem finite_physical_rounding_preserves_tangent_turn_sum
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (f E : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hE : ∀ i, ContDiff ℝ 1 (E i))
    (hd : ∀ i, deriv (E i) 1 = deriv (E (σ i)) 0)
    (hc : ∀ i, deriv (f i) 0 / deriv (f (σ.symm i)) 1 ∈ Complex.slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδq : δ < 1 / 4) (c : ι → ℂ)
    (hfpL : ∀ i t, t ∈ Icc (1 - δ) 1 → deriv (f (σ.symm i)) t ∈ physicalHalfplane (c i))
    (hfpR : ∀ i t, t ∈ Icc (0 : ℝ) δ → deriv (f i) t ∈ physicalHalfplane (c i))
    (hEpL : ∀ i t, t ∈ Icc (1 - δ) 1 → deriv (E (σ.symm i)) t ∈ physicalHalfplane (c i))
    (hEpR : ∀ i t, t ∈ Icc (0 : ℝ) δ → deriv (E i) t ∈ physicalHalfplane (c i))
    (hmid : ∀ i t, t ∈ Icc δ (1 - δ) → E i t = f i t)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = deriv (E i) t / (‖deriv (E i) t‖ : ℂ)) :
    (∑ i, (ψ i 1 - ψ i 0)) = (∑ i, (θ i 1 - θ i 0)) +
      ∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) := by
  let a : Icc (0 : ℝ) 1 := ⟨δ, hδ.le, by linarith⟩
  let b : Icc (0 : ℝ) 1 := ⟨1 - δ, by constructor <;> linarith⟩
  have hmiddleD (i : ι) (t : ℝ) (ht : t ∈ Icc δ (1 - δ)) : deriv (E i) t = deriv (f i) t :=
    physical_deriv_eq_of_eqOn_Icc (by linarith) ht
      ((hE i).differentiable (by norm_num) t) ((hf i).differentiable (by norm_num) t)
      (fun _ ht => hmid i _ ht)
  have hLmap (t : Icc (0 : ℝ) 1) : (unitIntervalAffine b 1 t : ℝ) ∈ Icc (1 - δ) 1 := by
    change 1 - δ ≤ (1 - δ) + (1 - (1 - δ)) * (t : ℝ) ∧
      (1 - δ) + (1 - (1 - δ)) * (t : ℝ) ≤ 1
    constructor <;> nlinarith [t.2.1, t.2.2]
  have hRmap (t : Icc (0 : ℝ) 1) : (unitIntervalAffine 0 a t : ℝ) ∈ Icc (0 : ℝ) δ := by
    change 0 ≤ 0 + (δ - 0) * (t : ℝ) ∧ 0 + (δ - 0) * (t : ℝ) ≤ δ
    constructor <;> nlinarith [t.2.1, t.2.2]
  have hcorner (i : ι) :
      (ψ (σ.symm i) 1 - ψ (σ.symm i) b) + (ψ i a - ψ i 0) =
        (θ (σ.symm i) 1 - θ (σ.symm i) b) + (θ i a - θ i 0) +
          Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) := by
    apply physical_corner_rounding_tangent_accounting
      (f (σ.symm i)) (f i) (E (σ.symm i)) (E i)
      (hf _) (hf _) (hE _) (hE _) a b (c i)
      (fun t => hfpL i _ (hLmap t)) (fun t => hfpR i _ (hRmap t))
      (fun t => hEpL i _ (hLmap t)) (fun t => hEpR i _ (hRmap t))
      (hmiddleD _ _ (by change 1 - δ ∈ Icc δ (1 - δ); constructor <;> linarith))
      (hmiddleD _ _ (by change δ ∈ Icc δ (1 - δ); constructor <;> linarith))
      (by simpa only [σ.apply_symm_apply] using hd (σ.symm i)) (hc i)
      (θ _) (θ _) (ψ _) (ψ _) (hθ _) (hθ _) (hψ _) (hψ _)
      (hθl _) (hθl _) (hψl _) (hψl _)
  have hmiddle (i : ι) : ψ i b - ψ i a = θ i b - θ i a := by
    have hmaps (t : Icc (0 : ℝ) 1) : (unitIntervalAffine a b t : ℝ) ∈ Icc δ (1 - δ) := by
      change δ ≤ δ + ((1 - δ) - δ) * (t : ℝ) ∧
        δ + ((1 - δ) - δ) * (t : ℝ) ≤ 1 - δ
      constructor <;> nlinarith [t.2.1, t.2.2]
    have he := euclidean_angle_lift_increment_eq
      ((hψ i).comp (unitIntervalAffine_continuous a b))
      ((hθ i).comp (unitIntervalAffine_continuous a b))
      (fun t => by
        apply Circle.ext
        change Complex.exp ((ψ i (unitIntervalAffine a b t) : ℂ) * Complex.I) =
          Complex.exp ((θ i (unitIntervalAffine a b t) : ℂ) * Complex.I)
        rw [hψl, hθl, hmiddleD i _ (hmaps t)]) (0 : Icc (0 : ℝ) 1) 1
    simpa only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one, Set.Icc.coe_zero, Set.Icc.coe_one] using he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hcorner i)
  simp only [Finset.sum_add_distrib] at hsum
  rw [σ.symm.sum_comp (fun i => ψ i 1 - ψ i b),
    σ.symm.sum_comp (fun i => θ i 1 - θ i b)] at hsum
  have hmidsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hmiddle i)
  simp only [Finset.sum_sub_distrib] at hsum hmidsum ⊢
  linarith

end RepulsiveCoulomb
