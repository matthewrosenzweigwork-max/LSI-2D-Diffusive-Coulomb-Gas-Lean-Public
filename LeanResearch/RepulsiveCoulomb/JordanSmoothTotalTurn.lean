import LeanResearch.RepulsiveCoulomb.JordanSupportingPoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-! Records-only extension candidate: actual smooth Jordan total turn ±2π,
reducing a constructed supporting point to the proved normalized support case.
This file is uncompiled and NOT part of the six-module phase-three inventory.
Finite corners and bounded-component orientation are still separate gaps. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem normalized_div_real_pos (z : ℂ) {c : ℝ} (hc : 0 < c) :
    (z / (c : ℂ)) / (‖z / (c : ℂ)‖ : ℂ) = z / (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.ofReal_div]
  field_simp

/-- Positive-speed support-point version; speed normalization is constructed. -/
theorem regular_simple_supported_loop_total_turn_positive_speed
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    {c : ℝ} (hc : 0 < c) (hbase : deriv γ 0 = (c : ℂ))
    (hsupport : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (γ r - γ 0).im)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ)) :
    θ 1 - θ 0 = 2 * Real.pi := by
  let η : ℝ → ℂ := fun t => γ t / (c : ℂ)
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hpη : Function.Periodic η 1 := by intro t; simp only [η, hp t]
  have hderiv (t : ℝ) : deriv η t = deriv γ t / (c : ℂ) := deriv_div_const _
  have hinjη : InjOn η (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    apply hinj hs ht
    have h := congrArg (fun z : ℂ => z * c) heq
    simpa only [η, div_mul_cancel₀ _ hcc] using h
  have hregη : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0 := by
    intro t ht
    rw [hderiv]
    exact div_ne_zero (hregular t ht) hcc
  have hbaseη : deriv η 0 = 1 := by rw [hderiv, hbase, div_self hcc]
  have hsupη : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (η r - η 0).im := by
    intro r hr
    simp only [η, ← sub_div, Complex.div_ofReal_im]
    exact div_nonneg (hsupport r hr) hc.le
  apply regular_simple_supported_loop_total_turn hη hpη hinjη hregη hbaseη hsupη hθ
  intro t
  rw [hderiv, normalized_div_real_pos _ hc]
  exact hlift t

private def reverseUnit (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem reverseUnit_continuous : Continuous reverseUnit :=
  (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- Negative-speed support-point version; reversing the actual curve reverses
its signed turn and gives the already proved positive-speed case. -/
theorem regular_simple_supported_loop_total_turn_negative_speed
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    {c : ℝ} (hc : c < 0) (hbase : deriv γ 0 = (c : ℂ))
    (hsupport : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (γ r - γ 0).im)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ)) :
    θ 1 - θ 0 = -(2 * Real.pi) := by
  let η : ℝ → ℂ := fun t => γ (1 - t)
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hpη : Function.Periodic η 1 := by
    intro t
    change γ (1 - (t + 1)) = γ (1 - t)
    have heq : 1 - (t + 1) = (1 - t) - 1 := by ring
    rw [heq, hp.sub_eq]
  have hderiv (t : ℝ) : deriv η t = -deriv γ (1 - t) := by
    change deriv (fun t : ℝ => γ (1 - t)) t = _
    exact deriv_comp_const_sub _ _ _
  have hinjη : InjOn η (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    have h := periodic_simple_loop_injOn_Ioc hp hinj
      (show 1 - s ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show 1 - t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) heq
    linarith
  have hregη : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0 := by
    intro t ht
    rw [hderiv]
    exact neg_ne_zero.mpr (hregular _ (by constructor <;> linarith [ht.1, ht.2]))
  have hbaseη : deriv η 0 = ((-c : ℝ) : ℂ) := by
    rw [hderiv, sub_zero, periodic_loop_deriv_one_eq_zero hp, hbase, Complex.ofReal_neg]
  have h10 : γ 1 = γ 0 := by simpa using hp 0
  have hsupη : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (η r - η 0).im := by
    intro r hr
    simp only [η, sub_zero, h10]
    exact hsupport _ (by constructor <;> linarith [hr.1, hr.2])
  let φ : Icc (0 : ℝ) 1 → ℝ := fun t => θ (reverseUnit t) + Real.pi
  have hφ : Continuous φ := (hθ.comp reverseUnit_continuous).add continuous_const
  have hφlift (t : Icc (0 : ℝ) 1) :
      Complex.exp ((φ t : ℂ) * Complex.I) = deriv η t / (‖deriv η t‖ : ℂ) := by
    simp only [φ, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
      mul_neg_one, hderiv, norm_neg, neg_div]
    exact congrArg Neg.neg (hlift (reverseUnit t))
  have ht := regular_simple_supported_loop_total_turn_positive_speed hη hpη hinjη hregη
    (neg_pos.mpr hc) hbaseη hsupη hφ hφlift
  have hr0 : reverseUnit 0 = 1 := by apply Subtype.ext; simp [reverseUnit]
  have hr1 : reverseUnit 1 = 0 := by apply Subtype.ext; simp [reverseUnit]
  change (θ (reverseUnit 1) + Real.pi) - (θ (reverseUnit 0) + Real.pi) = _ at ht
  rw [hr0, hr1] at ht
  linarith

/-- Actual periodic real tangent lifts have basepoint-independent increments. -/
theorem periodic_tangent_angle_increment {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    (hreg : ∀ t : ℝ, deriv γ t ≠ 0)
    {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (hlift : ∀ t, Circle.exp (Φ t) = euclideanDirection (deriv γ t) (hreg t)) (a : ℝ) :
    Φ (a + 1) - Φ a = Φ 1 - Φ 0 := by
  have hper (t : ℝ) : Circle.exp (Φ (t + 1)) = Circle.exp (Φ t) := by
    rw [hlift, hlift]
    apply Circle.ext
    simp only [euclideanDirection_coe, periodic_loop_deriv_periodic hp t]
  have hcont : Continuous (fun t => Φ (t + 1) - Φ t) :=
    (hΦ.comp (continuous_id.add continuous_const)).sub hΦ
  have he (t : ℝ) : Circle.exp (Φ (t + 1) - Φ t) = 1 := by
    rw [Circle.exp_sub, hper, div_self']
  have h := Circle.isCoveringMap_exp.const_of_comp hcont
    (by intro a b; exact (he a).trans (he b).symm) a 0
  simpa only [zero_add] using h

/-- The actual tangent angle of every regular C¹ periodic simple plane loop
has increment `2π` or `−2π`. A support point is constructed by compactness. -/
theorem regular_simple_periodic_loop_total_turn
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ)) :
    θ 1 - θ 0 = 2 * Real.pi ∨ θ 1 - θ 0 = -(2 * Real.pi) := by
  have hreg := periodic_loop_regular_everywhere hp hregular
  obtain ⟨Φ, hΦ, _, hΦlift⟩ := exists_euclidean_angle_lift hγ.continuous_deriv_one hreg
    0 (Complex.arg (deriv γ 0)) (by
      rw [← euclideanDirection_arg (deriv γ 0) (hreg 0)]
      exact Circle.exp_arg _)
  have hθΦ : θ 1 - θ 0 = Φ 1 - Φ 0 := by
    have hcont : Continuous (fun t : Icc (0 : ℝ) 1 => Φ t) := hΦ.comp continuous_subtype_val
    have h := euclidean_angle_lift_increment_eq hθ hcont
      (fun t => by
        change Circle.exp (θ t) = Circle.exp (Φ t)
        rw [hΦlift]
        apply Circle.ext
        exact hθlift t)
      (0 : Icc (0 : ℝ) 1) 1
    simpa using h
  obtain ⟨a, ha, him, hre, hsupport⟩ := exists_regular_periodic_horizontal_support hγ hp hregular
  let η : ℝ → ℂ := fun t => γ (t + a)
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hpη : Function.Periodic η 1 := by
    intro t
    change γ (t + 1 + a) = γ (t + a)
    rw [show t + 1 + a = t + a + 1 by ring, hp]
  have hinjη := periodic_simple_loop_shift_injOn hp hinj ha
  have hderiv (t : ℝ) : deriv η t = deriv γ (t + a) := deriv_comp_add_const _ _ _
  have hregη : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0 := by
    intro t _
    rw [hderiv]
    exact hreg _
  have hbase : deriv η 0 = ((deriv γ a).re : ℂ) := by
    rw [hderiv, zero_add]
    apply Complex.ext <;> simp [him]
  have hsupη : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (η r - η 0).im := by
    intro r _
    simpa only [η, zero_add] using hsupport (r + a)
  let φ : Icc (0 : ℝ) 1 → ℝ := fun t => Φ (t + a)
  have hφ : Continuous φ := hΦ.comp (continuous_subtype_val.add continuous_const)
  have hφlift (t : Icc (0 : ℝ) 1) : Complex.exp ((φ t : ℂ) * Complex.I) =
      deriv η t / (‖deriv η t‖ : ℂ) := by
    rw [hderiv]
    exact congrArg (fun z : Circle => (z : ℂ)) (hΦlift (t + a))
  have hinc : φ 1 - φ 0 = Φ 1 - Φ 0 := by
    simpa [φ, add_comm] using periodic_tangent_angle_increment hp hreg hΦ hΦlift a
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · right
    rw [hθΦ, ← hinc]
    exact regular_simple_supported_loop_total_turn_negative_speed hη hpη hinjη hregη
      hneg hbase hsupη hφ hφlift
  · left
    rw [hθΦ, ← hinc]
    exact regular_simple_supported_loop_total_turn_positive_speed hη hpη hinjη hregη
      hpos hbase hsupη hφ hφlift

end RepulsiveCoulomb
