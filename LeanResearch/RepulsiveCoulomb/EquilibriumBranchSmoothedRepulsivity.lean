module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSmoothedMoments
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEmpiricalRepulsivity

@[expose] public section

/-! Genuine common-measure Coulomb positivity after smearing both the empirical
and reference measures. Mass, cap, P2, absolute energies, nonatomicity and support
separation are derived for the actual smoothed reference. The later double-kernel
identification must still transport all three terms, not only particle pairs. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumReference_smoothed_logEnergy_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)).prod
        (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) := by
  let ρ := equilibriumSmoothedDensity ε R.density
  have hρm : Measurable ρ := equilibriumSmoothedDensity_measurable ε R.smooth.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumSmoothedDensity_nonneg ε (fun x => (R.positive x).le)
  have hρM : ∀ x, ρ x ≤ Real.pi⁻¹ := equilibriumSmoothedDensity_le ε R.smooth.continuous.measurable
    (fun x => (R.positive x).le) R.cap
  obtain ⟨hρi, hρmass⟩ := equilibriumReference_smoothed_mass R ε
  have hρ2 := equilibriumReference_smoothed_density_secondMoment hβ R hε
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  exact equilibriumDensityMeasure_logEnergy_integrable hρm hρ0
    (equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL hρm hρ0 hρM hρi hρmass hρL)

/-- Actual positivity of P_epsilon(mu_N)-P_epsilon(mu_beta). Every measure-class
and finite-energy input is proved; the circular and planar parts are not confused. -/
theorem equilibriumReference_double_smoothed_repulsive {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumCircleEmpirical z ε).prod (equilibriumCircleEmpirical z ε)) -
      2 * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂(equilibriumCircleEmpirical z ε).prod
          (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) +
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂(equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)).prod
          (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) := by
  let μs := equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)
  letI := equilibriumCircleEmpirical_probability hN z ε
  letI := equilibriumCircleEmpirical_nullSingleton z hε
  letI : IsProbabilityMeasure μs := equilibriumReference_smoothed_probability R ε
  have hAC : μs ≪ volume := equilibriumDensityMeasure_absolutelyContinuous _
  letI : NullSingletonClass μs := ⟨fun x => hAC (measure_singleton x)⟩
  have hμnorm : Integrable (fun x : ℂ => ‖x‖) μs :=
    equilibriumMeasure_norm_integrable_of_secondMoment
      (equilibriumReference_smoothed_secondMoment_integrable hβ R hε.le)
  exact equilibriumMutuallySingular_logRepulsive
    (equilibriumCircleEmpiricalSupport_measurable z ε)
    (equilibriumCircleEmpirical_supported z hε.le)
    (hAC (equilibriumCircleEmpiricalSupport_volume_zero z ε))
    (equilibriumCircleEmpirical_logEnergy_integrable hN z hε)
    (equilibriumCircleEmpirical_cross_integrable hN z hε hμnorm)
    (equilibriumReference_smoothed_logEnergy_integrable hβ R hε.le)

end RepulsiveCoulomb
