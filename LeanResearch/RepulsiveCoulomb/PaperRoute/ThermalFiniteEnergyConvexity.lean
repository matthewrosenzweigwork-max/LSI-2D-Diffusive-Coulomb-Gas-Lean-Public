import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalInteractionConvexity
import LeanResearch.RepulsiveCoulomb.PaperRoute.LogGreenZeroMass

/-! Discharge the smooth Green premise by the NEW
zero-mass producer, then specialize the capped-density passage to the literal
finite canonical-objective domain. No limiting cross-energy premise appears. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

theorem thermalSmoothGreenNonnegative_proved : ThermalSmoothGreenNonnegative := by
  intro η hη hηc hmass
  simpa only [thermalDensityLogEnergy, thermalDensityLogIntegrand, equilibriumLogKernel] using
    log_interaction_zero_mass_nonneg (hη.of_le (by norm_num)) hηc hmass

/-- Actual finite-canonical-domain interaction convexity. The mixed self-energy
is proved integrable by the new capped approximation and interaction-liminf
route. Both original self energies are derived from objective finiteness. -/
theorem thermalInteraction_convex_on_finite_canonical_domain
    {β t : ℝ} (hβ : 0 < β) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : ProbabilityMeasure ℂ)
    (hμF : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hνF : equilibriumNonnegativeObjective β ν ≠ ∞) :
    ∃ ξ : ProbabilityMeasure ℂ,
      (ξ : Measure ℂ) = equilibriumDensityMeasure
        (thermalDensityMixture t (equilibriumReferenceDensity μ) (equilibriumReferenceDensity ν)) ∧
      (ξ : Measure ℂ) = ENNReal.ofReal t • (μ : Measure ℂ) + ENNReal.ofReal (1 - t) • (ν : Measure ℂ) ∧
      (ξ : Measure ℂ) ≪ volume ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2) ξ ∧
      Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) ((ξ : Measure ℂ).prod ξ) ∧
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((ξ : Measure ℂ).prod ξ)) ≤
        t * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((μ : Measure ℂ).prod μ)) +
        (1 - t) * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((ν : Measure ℂ).prod ν)) := by
  have hμAC := equilibriumObjective_finite_absolutelyContinuous hβ hμF
  have hνAC := equilibriumObjective_finite_absolutelyContinuous hβ hνF
  have hμP2 := equilibriumObjective_finite_secondMoment hμF
  have hνP2 := equilibriumObjective_finite_secondMoment hνF
  let ρ := equilibriumReferenceDensity (μ : Measure ℂ)
  let σ := equilibriumReferenceDensity (ν : Measure ℂ)
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hσm : Measurable σ := equilibriumReferenceDensity_measurable ν
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hσ0 : ∀ x, 0 ≤ σ x := equilibriumReferenceDensity_nonneg ν
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hσi : Integrable σ := equilibriumReferenceDensity_integrable ν
  have hρmass : (∫ x, ρ x) = 1 := integral_equilibriumReferenceDensity hμAC
  have hσmass : (∫ x, σ x) = 1 := integral_equilibriumReferenceDensity hνAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hμAC hμP2
  have hσ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * σ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hνAC hνP2
  have hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume) :=
    thermalReferenceDensity_logIntegrand_integrable hβ hμF
  have hσG : Integrable (thermalDensityLogIntegrand σ) (volume.prod volume) :=
    thermalReferenceDensity_logIntegrand_integrable hβ hνF
  let m := thermalDensityMixture t ρ σ
  have hmm : Measurable m := thermalDensityMixture_measurable hρm hσm t
  have hm0 : ∀ x, 0 ≤ m x := thermalDensityMixture_nonneg hρ0 hσ0 ht0 ht1
  have hmi : Integrable m := thermalDensityMixture_integrable hρi hσi t
  have hmass : (∫ x, m x) = 1 := thermalDensityMixture_integral hρi hσi hρmass hσmass t
  let ξ : ProbabilityMeasure ℂ := thermalProbabilityOfDensity hm0 hmi hmass
  obtain ⟨hGm, hconv⟩ := thermalDensityLogEnergy_convex_finite_domain_of_smoothGreen
    thermalSmoothGreenNonnegative_proved hρm hσm hρ0 hσ0 hρi hσi hρmass hσmass
    hρ2 hσ2 hρG hσG ht0 ht1
  have hξG : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((ξ : Measure ℂ).prod ξ) :=
    (thermalDensityLogIntegrand_integrable_iff hmm hm0).mp hGm
  refine ⟨ξ, rfl, ?_, equilibriumDensityMeasure_absolutelyContinuous m, ?_, hξG, ?_⟩
  · change equilibriumDensityMeasure (thermalDensityMixture t (equilibriumReferenceDensity μ)
      (equilibriumReferenceDensity ν)) = _
    rw [thermalDensityMixture_measure hρm hσm hρ0 hσ0 ht0 ht1,
      equilibriumReferenceDensity_measure hμAC, equilibriumReferenceDensity_measure hνAC]
  · exact (equilibriumDensityMeasure_integrable_iff hmm hm0 _).mpr
      (thermalDensityMixture_secondMoment_integrable hρ2 hσ2 t)
  · have heμ : thermalDensityLogEnergy ρ =
        ∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((μ : Measure ℂ).prod μ) := by
      have h := integral_thermalDensityLogIntegrand hρm hρ0 hρG
      rw [equilibriumReferenceDensity_measure hμAC] at h
      exact h.symm
    have heν : thermalDensityLogEnergy σ =
        ∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((ν : Measure ℂ).prod ν) := by
      have h := integral_thermalDensityLogIntegrand hσm hσ0 hσG
      rw [equilibriumReferenceDensity_measure hνAC] at h
      exact h.symm
    change (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((equilibriumDensityMeasure m).prod (equilibriumDensityMeasure m))) ≤ _
    rw [integral_thermalDensityLogIntegrand hmm hm0 hGm]
    simpa only [heμ, heν] using hconv

end RepulsiveCoulomb.PaperRoute
