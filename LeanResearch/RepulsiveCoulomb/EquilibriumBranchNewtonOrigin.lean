import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonCircleIdentity

/-! Exact origin increment of a bounded measurable radial logarithmic
potential. The checked circular-error mass gives a quadratic bound with the
actual constant M*pi/2, before density continuity is known. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumCircularError_mul_integrable {r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ} {M : ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρM : ∀ y, ρ y ≤ M) : Integrable (fun y : ℂ => equilibriumCircularError r y * ρ y) := by
  apply ((equilibriumCircularError_integrable hr).mul_const M).mono'
    ((equilibriumCircularError_measurable r).mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    change ‖equilibriumCircularError r y * ρ y‖ ≤ equilibriumCircularError r y * M
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (equilibriumCircularError_nonneg r y) (hρ0 y))]
    exact mul_le_mul_of_nonneg_left (hρM y) (equilibriumCircularError_nonneg r y))

theorem integral_equilibriumCircularError_mul_bound {r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ} {M : ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρM : ∀ y, ρ y ≤ M) :
    0 ≤ (∫ y : ℂ, equilibriumCircularError r y * ρ y) ∧
      (∫ y : ℂ, equilibriumCircularError r y * ρ y) ≤ M * Real.pi * r ^ 2 / 2 := by
  refine ⟨integral_nonneg (fun y => mul_nonneg (equilibriumCircularError_nonneg r y) (hρ0 y)), ?_⟩
  have h := integral_mono (equilibriumCircularError_mul_integrable hr hρm hρ0 hρM)
    ((equilibriumCircularError_integrable hr).mul_const M)
    (fun y => mul_le_mul_of_nonneg_left (hρM y) (equilibriumCircularError_nonneg r y))
  rw [integral_mul_const, integral_equilibriumCircularError hr] at h
  nlinarith

/-- Exact radial potential increment, with the planar-zero point removed
before identifying the real logarithm with its circular error. -/
theorem equilibriumDensityPotential_origin_difference {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    {x : ℂ} (hx : x ≠ 0) :
    equilibriumDensityPotential ρ 0 - equilibriumDensityPotential ρ x =
      ∫ y : ℂ, equilibriumCircularError ‖x‖ y * ρ y := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hk : Integrable (fun y : ℂ => equilibriumLogKernel y * ρ y) := by
    simpa only [equilibriumLogKernel, zero_sub, norm_neg] using
      equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi hρL (0 : ℂ)
  have he := equilibriumCircularError_mul_integrable hr hρm hρ0 hρM
  have hreg : Integrable (fun y : ℂ => equilibriumCircularKernel ‖x‖ y * ρ y) := by
    apply (hk.sub he).congr
    filter_upwards [volume.ae_ne (0 : ℂ)] with y hy
    dsimp only [Pi.sub_apply]
    rw [equilibriumCircularError_eq_sub hr hy]
    ring
  have heq : (fun y : ℂ => equilibriumCircularError ‖x‖ y * ρ y) =ᵐ[volume]
      (fun y : ℂ => equilibriumLogKernel y * ρ y - equilibriumCircularKernel ‖x‖ y * ρ y) := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with y hy
    rw [equilibriumCircularError_eq_sub hr hy]
    ring
  rw [equilibriumDensityPotential_newton_circle hρm hρ0 hρi hρmass hρ2 hUrad hx,
    integral_congr_ae heq, integral_sub hk hreg]
  congr 1
  unfold equilibriumDensityPotential
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp only [equilibriumLogKernel, zero_sub, norm_neg])

/-- The genuine quadratic origin estimate, sufficient to obtain derivative
zero and continuity of the eventual gradient at the origin. -/
theorem equilibriumDensityPotential_origin_quadratic {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    (x : ℂ) :
    0 ≤ equilibriumDensityPotential ρ 0 - equilibriumDensityPotential ρ x ∧
      |equilibriumDensityPotential ρ x - equilibriumDensityPotential ρ 0| ≤ M * Real.pi * ‖x‖ ^ 2 / 2 := by
  by_cases hx : x = 0
  · subst x
    simp only [sub_self, abs_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div, le_refl, and_self]
  · have he := equilibriumDensityPotential_origin_difference hρm hρ0 hρM hρi hρmass hρ2 hUrad hx
    have hb := integral_equilibriumCircularError_mul_bound (norm_pos_iff.mpr hx) hρm hρ0 hρM
    rw [← he] at hb
    refine ⟨hb.1, ?_⟩
    rw [abs_of_nonpos (by linarith [hb.1])]
    linarith [hb.2]

end RepulsiveCoulomb
