import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialPotential
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalBoundedRepresentative

/-! Apply the conditional finite-canonical-minimizer to
bounded EL representative theorem to NEW minimizers, then derive actual
pointwise radiality of that selected positive representative from the NEW
invariant measure and genuine potential. No old selected thermal reference or
old EL-radiality/regularity producer is used. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Every point potential of an actual bounded P² density is integrable under
its literal density law. This is established before using its real value. -/
theorem thermalBoundedDensity_pointPotential_integrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2 * ρ y)) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) (equilibriumDensityMeasure ρ) := by
  apply (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr
  exact equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi
    (equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2) x

/-- Exact physical-density potential of the supplied bounded representative,
with both genuine integrability and the extended/real equality derived. -/
theorem thermalBoundedDensity_extendedPotential_eq_potential
    (μ : ProbabilityMeasure ℂ) {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2 * ρ y))
    (hρlaw : equilibriumDensityMeasure ρ = (μ : Measure ℂ)) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ ∧
      thermalExtendedLogPotential μ x = (equilibriumDensityPotential ρ x : EReal) := by
  have hG : Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ := by
    rw [← hρlaw]
    exact thermalBoundedDensity_pointPotential_integrable hρm hρ0 hρM hρi hρ2 x
  have hAC : (μ : Measure ℂ) ≪ volume := hρlaw ▸ equilibriumDensityMeasure_absolutelyContinuous ρ
  refine ⟨hG, ?_⟩
  rw [thermalExtendedLogPotential_eq_integral μ hAC x hG]
  congr 1
  rw [← hρlaw, integral_equilibriumDensityMeasure hρm hρ0]
  unfold equilibriumDensityPotential
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by ring

/-- Pointwise potential radiality is justified for the actual bounded density
representative of a NEW original canonical minimizer. -/
theorem thermalCanonical_bounded_density_potential_radial {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν)
    {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2 * ρ y))
    (hρlaw : equilibriumDensityMeasure ρ = (μ : Measure ℂ)) :
    ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
  intro x y hxy
  have h := (thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq hβ μ hmin hxy).2.2
  rw [(thermalBoundedDensity_extendedPotential_eq_potential μ hρm hρ0 hρM hρi hρ2 hρlaw x).2,
    (thermalBoundedDensity_extendedPotential_eq_potential μ hρm hρ0 hρM hρi hρ2 hρlaw y).2] at h
  exact EReal.coe_injective h

/-- Conditional EL production is applied only to the NEW finite canonical
minimizer. Radiality is then derived for the actual positive pointwise-EL
representative, not for an arbitrary RN version. -/
theorem thermalCanonical_minimizer_exists_bounded_radial_EL_density {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
      Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
      Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
      Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
      equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
      (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
      0 < K ∧ (∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) ∧
      (∀ x, Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ) ∧
      (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) ∧
      (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) := by
  have hfinite := (thermalCanonical_global_minimizer_finite_domain hβ hmin).2.2
  obtain ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρlaw, hEL, hK, htail⟩ :=
    equilibriumCanonicalMinimizer_exists_bounded_EL_density hβ μ hfinite hmin
  have hρ0 (x : ℂ) : 0 ≤ ρ x := (hρpos x).le
  have hUrad := thermalCanonical_bounded_density_potential_radial hβ μ hmin
    hρm hρ0 hρM hρi hρ2 hρlaw
  refine ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρlaw,
    hEL, hK, htail, ?_, hUrad, ?_⟩
  · intro x
    exact (thermalBoundedDensity_extendedPotential_eq_potential μ hρm hρ0 hρM hρi hρ2 hρlaw x).1
  · intro x y hxy
    apply Real.log_injOn_pos (hρpos x) (hρpos y)
    rw [hEL x, hEL y, hxy, hUrad hxy]

/-- Actual original-input existence of a positive bounded radial pointwise-EL
representative with the zeroth-order Gaussian-polynomial tail. This does not
select an old constructed or already regular thermal reference. -/
theorem thermal_exists_bounded_radial_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      (∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) ∧
      ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
        Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
        Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
        Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
        Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
        equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
        (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
        0 < K ∧ (∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) ∧
        (∀ x, Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ) ∧
        (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) ∧
        (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) := by
  obtain ⟨μ, _, _, hfinite, hmin⟩ := thermalCanonical_exists_global_minimizer hβ
  exact ⟨μ, hfinite, hmin, thermalCanonical_minimizer_exists_bounded_radial_EL_density hβ μ hmin⟩

end RepulsiveCoulomb.PaperRoute
