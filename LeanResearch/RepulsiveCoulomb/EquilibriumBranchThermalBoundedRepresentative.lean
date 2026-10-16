module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchELRepresentative

@[expose] public section

/-! Actual bounded pointwise-EL densities for the attained minimizers. All
properties are derived from finite objective and canonical minimization;
there is no assumed equilibrium package. The sharp cap, uniqueness and
smooth radial structure remain subsequent conclusions. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Every actual finite-objective minimizer has a strictly positive bounded
representative with pointwise EL and the exact zeroth-order manuscript tail. -/
theorem equilibriumCanonicalMinimizer_exists_bounded_EL_density {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
      Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
      Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
      Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
      equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
      (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
      0 < K ∧ (∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) := by
  let r : ℂ → ℝ := equilibriumReferenceDensity μ
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hfinite
  have hP2 := equilibriumObjective_finite_secondMoment hfinite
  have hrm : Measurable r := equilibriumReferenceDensity_measurable μ
  have hr0 : ∀ x, 0 ≤ r x := equilibriumReferenceDensity_nonneg μ
  have hri : Integrable r := equilibriumReferenceDensity_integrable μ
  have hrmass : (∫ x : ℂ, r x) = 1 := integral_equilibriumReferenceDensity hAC
  have hr2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * r x) :=
    equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hrH : Integrable (fun x : ℂ => r x * Real.log (r x)) :=
    equilibriumObjective_finite_entropy_integrable hβ hfinite
  have hrmeasure : equilibriumDensityMeasure r = (μ : Measure ℂ) := equilibriumReferenceDensity_measure hAC
  have hrGμ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure r).prod (equilibriumDensityMeasure r)) := by
    rw [hrmeasure]
    exact equilibriumObjective_finite_logEnergy_integrable hβ hfinite
  have hrG := equilibriumDensityMeasure_energy_to_density hrm hr0 hrGμ
  have hrpos : ∀ᵐ x : ℂ, 0 < r x := equilibriumCanonicalMinimizer_density_positive_ae hβ μ hfinite hmin
  obtain ⟨C, hEL⟩ := equilibriumCanonicalMinimizer_eulerLagrange_ae hβ μ hfinite hmin
  let ρ := equilibriumELRepresentative β C r
  let M : ℝ := Real.exp (C + β * ((∫ y : ℂ, equilibriumLogMoment y * r y) + 1))
  let K : ℝ := Real.exp (C + β * (∫ y : ℂ, equilibriumLogMoment y * r y))
  have hρr : ρ =ᵐ[volume] r := equilibriumELRepresentative_ae_eq hrpos hEL
  have hp := equilibriumELRepresentative_pointwise_properties hβ hrm hr0 hri hrmass hr2 hrpos hrG hEL
  have hρmeasure : equilibriumDensityMeasure ρ = (μ : Measure ℂ) := by
    calc
      equilibriumDensityMeasure ρ = equilibriumDensityMeasure r := by
        unfold equilibriumDensityMeasure
        apply withDensity_congr_ae
        exact hρr.mono (fun x hx => by simp only [hx])
      _ = μ := hrmeasure
  refine ⟨ρ, C, M, K, equilibriumELRepresentative_measurable β C hrm,
    equilibriumELRepresentative_pos β C r, Real.exp_pos _, hp.2.2,
    hri.congr hρr.symm, ?_, ?_, ?_, hρmeasure, hp.1, Real.exp_pos _, hp.2.1⟩
  · rw [integral_congr_ae hρr]
    exact hrmass
  · exact hr2.congr (hρr.symm.mono (fun x hx => by simp only [hx]))
  · exact hrH.congr (hρr.symm.mono (fun x hx => by simp only [hx]))

/-- Every beta>0 admits an actual globally minimizing probability with a
positive bounded density and a pointwise Euler--Lagrange equation. -/
theorem equilibrium_exists_bounded_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ (μ : ProbabilityMeasure ℂ) (ρ : ℂ → ℝ) (C M : ℝ),
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
      Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
      Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
      equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
      (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, hAC, hP2, hfinite, hmin⟩ := equilibriumCanonical_exists_global_minimizer hβ
  obtain ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρμ, hEL, hK, htail⟩ :=
    equilibriumCanonicalMinimizer_exists_bounded_EL_density hβ μ hfinite hmin
  exact ⟨μ, ρ, C, M, hfinite, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρμ, hEL, hmin⟩

end RepulsiveCoulomb
