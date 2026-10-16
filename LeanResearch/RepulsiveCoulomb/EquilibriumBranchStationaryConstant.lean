import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The final measure-theoretic step in Euler--Lagrange identification.
An actual integrable chemical potential annihilating bounded, measurable,
zero-mass variations is constant almost everywhere. The variation identity
itself is proved separately from minimization, never postulated for the
thermal equilibrium construction. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

/-- Centered indicators suffice to identify the chemical potential, with a
uniform test bound one. This is valid on any probability space. -/
theorem equilibrium_stationary_integrable_ae_constant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {q : α → ℝ} (hq : Integrable q μ)
    (hstation : ∀ φ : α → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂μ) = 0 → (∫ x, q x * φ x ∂μ) = 0) :
    q =ᵐ[μ] (fun _ => ∫ x, q x ∂μ) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq q (fun _ => ∫ x, q x ∂μ)
    hq (integrable_const _)
  intro A hA _
  let φ : α → ℝ := fun x => A.indicator (fun _ => (1 : ℝ)) x - μ.real A
  have hφm : Measurable φ := (measurable_const.indicator hA).sub measurable_const
  have hφb : ∀ x, |φ x| ≤ 1 := by
    intro x
    have hp0 : 0 ≤ μ.real A := measureReal_nonneg
    have hp1 : μ.real A ≤ 1 := measureReal_le_one
    by_cases hx : x ∈ A
    · dsimp only [φ]
      rw [Set.indicator_of_mem hx, abs_of_nonneg (sub_nonneg.mpr hp1)]
      linarith
    · dsimp only [φ]
      rw [Set.indicator_of_notMem hx, zero_sub, abs_neg, abs_of_nonneg hp0]
      exact hp1
  have hφzero : (∫ x, φ x ∂μ) = 0 := by
    change (∫ x, A.indicator (fun _ => (1 : ℝ)) x - μ.real A ∂μ) = 0
    rw [integral_sub ((integrable_const (μ := μ) (1 : ℝ)).indicator hA) (integrable_const _),
      integral_indicator_const 1 hA]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, mul_one, sub_self]
  have hzero := hstation φ hφm hφb hφzero
  have hid : (fun x => q x * φ x) =
      (fun x => A.indicator q x - μ.real A * q x) := by
    funext x
    dsimp only [φ]
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      ring
    · simp only [Set.indicator_of_notMem hx]
      ring
  rw [hid, integral_sub (hq.indicator hA) (hq.const_mul _),
    integral_indicator hA, integral_const_mul] at hzero
  rw [setIntegral_const, smul_eq_mul]
  linarith

end RepulsiveCoulomb
