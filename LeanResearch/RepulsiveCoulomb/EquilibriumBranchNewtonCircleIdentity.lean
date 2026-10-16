module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchELRadiality
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEnergy

@[expose] public section

/-! The actual radial Newton formula obtained from a singular circle average.
The circle/background cross energy is genuinely absolutely integrable by the
checked CircleEnergy estimate. No density continuity is used. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
namespace RepulsiveCoulomb

theorem equilibriumDensityPotential_radial_of_EL {β C : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    {x y : ℂ} (hxy : ‖x‖ = ‖y‖) : equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
  have hl := congrArg Real.log (hρrad hxy)
  rw [hEL x, hEL y, hxy] at hl
  have he : β * equilibriumDensityPotential ρ x = β * equilibriumDensityPotential ρ y := by linarith
  exact (mul_left_cancel₀ hβ.ne') he

/-- Literal density convolution equals the integral under its actual law. -/
theorem equilibriumDensityPotential_eq_measureIntegral {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (x : ℂ) :
    equilibriumDensityPotential ρ x =
      ∫ y : ℂ, equilibriumLogKernel (x - y) ∂equilibriumDensityMeasure ρ := by
  rw [integral_equilibriumDensityMeasure hρm hρ0]
  unfold equilibriumDensityPotential
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by ring)

/-- The actual Newton cutoff formula at every nonzero radius, derived from
radiality and Fubini, before any continuity assumption on the density. -/
theorem equilibriumDensityPotential_newton_circle {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    {x : ℂ} (hx : x ≠ 0) :
    equilibriumDensityPotential ρ x = ∫ y : ℂ, equilibriumCircularKernel ‖x‖ y * ρ y := by
  let μ := equilibriumDensityMeasure ρ
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hμ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ :=
    (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr hρ2
  have hμ1 : Integrable (fun y : ℂ => ‖y‖) μ := by
    apply (hμ2.add (integrable_const (μ := μ) (1 : ℝ))).mono' continuous_norm.measurable.aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      nlinarith [sq_nonneg (‖y‖ - 1)])
  have hcross := equilibriumMeasure_circle_logEnergy_integrable hμ1 (0 : ℂ) hr
  have hswap : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleMeasure 0 ‖x‖).prod μ) := by
    apply hcross.swap.congr
    exact Eventually.of_forall (fun p => by
      change equilibriumLogKernel (p.2 - p.1) = equilibriumLogKernel (p.1 - p.2)
      simp only [equilibriumLogKernel, norm_sub_rev])
  have hc : (∫ z : ℂ, equilibriumDensityPotential ρ z ∂equilibriumCircleMeasure 0 ‖x‖) =
      equilibriumDensityPotential ρ x := by
    apply integral_eq_const
    have hs : ∀ᵐ z ∂equilibriumCircleMeasure 0 ‖x‖, z ∈ sphere (0 : ℂ) ‖x‖ :=
      mem_ae_iff.mpr (equilibriumCircleMeasure_supported 0 hr.le)
    filter_upwards [hs] with z hz
    apply hUrad
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  calc
    equilibriumDensityPotential ρ x =
        ∫ z : ℂ, equilibriumDensityPotential ρ z ∂equilibriumCircleMeasure 0 ‖x‖ := hc.symm
    _ = ∫ z : ℂ, ∫ y : ℂ, equilibriumLogKernel (z - y) ∂μ ∂equilibriumCircleMeasure 0 ‖x‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall (equilibriumDensityPotential_eq_measureIntegral hρm hρ0)
    _ = ∫ y : ℂ, ∫ z : ℂ, equilibriumLogKernel (z - y) ∂equilibriumCircleMeasure 0 ‖x‖ ∂μ :=
      integral_integral_swap hswap
    _ = ∫ y : ℂ, equilibriumCircularKernel ‖x‖ (0 - y) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => equilibriumCircleMeasure_log_potential 0 y hr)
    _ = ∫ y : ℂ, equilibriumCircularKernel ‖x‖ y * ρ y := by
      rw [integral_equilibriumDensityMeasure hρm hρ0]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        simp only [equilibriumCircularKernel, zero_sub, norm_neg]
        ring)

end RepulsiveCoulomb
