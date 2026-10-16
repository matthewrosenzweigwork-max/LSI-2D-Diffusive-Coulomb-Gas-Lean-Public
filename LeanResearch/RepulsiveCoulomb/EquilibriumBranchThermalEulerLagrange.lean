module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalPositivity
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityStationarity

@[expose] public section

/-! Actual Euler--Lagrange identification for a thermal minimizer, first in
its correct planar-a.e. form. Positivity and every finite variation-domain
condition are derived from minimization and the finite nonnegative objective.
Radiality, boundedness, smoothness and pointwise EL are later consequences. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The canonical RN density of every actual finite-objective minimizer obeys
the manuscript Euler--Lagrange equation planar-a.e., with a finite real
constant and the actual logarithmic convolution. -/
theorem equilibriumCanonicalMinimizer_eulerLagrange_ae {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ C : ℝ, ∀ᵐ x : ℂ,
      Real.log (equilibriumReferenceDensity μ x) =
        -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential (equilibriumReferenceDensity μ) x) + C := by
  let ρ : ℂ → ℝ := equilibriumReferenceDensity μ
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hfinite
  have hP2 := equilibriumObjective_finite_secondMoment hfinite
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hρmass : (∫ x : ℂ, ρ x) = 1 := integral_equilibriumReferenceDensity hAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) :=
    equilibriumObjective_finite_entropy_integrable hβ hfinite
  have hρmeasure : equilibriumDensityMeasure ρ = (μ : Measure ℂ) := equilibriumReferenceDensity_measure hAC
  have hρGμ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
    rw [hρmeasure]
    exact equilibriumObjective_finite_logEnergy_integrable hβ hfinite
  have hRR := equilibriumDensityMeasure_energy_to_density hρm hρ0 hρGμ
  have hminρ : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤ equilibriumCanonicalFreeEnergy β ν := by
    intro ν
    rw [hρmeasure]
    exact hmin ν
  have hconst := equilibriumDensityMinimizer_chemicalPotential_constant hβ hρm hρ0 hρi hρmass
    hρ2 hρH hRR hminρ
  have hpos : ∀ᵐ x : ℂ, 0 < ρ x := equilibriumCanonicalMinimizer_density_positive_ae hβ μ hfinite hmin
  have hvol : (volume : Measure ℂ) ≪ equilibriumDensityMeasure ρ :=
    withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
      (hpos.mono (fun x hx => (ENNReal.ofReal_pos.mpr hx).ne'))
  have hconstvol := hvol.ae_eq hconst
  let c : ℝ := ∫ x : ℂ, equilibriumChemicalPotential β ρ x ∂equilibriumDensityMeasure ρ
  refine ⟨β * c, ?_⟩
  filter_upwards [hconstvol] with x hx
  change ‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x + Real.log (ρ x) / β = c at hx
  have hlog : Real.log (ρ x) / β = c - (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) := by linarith
  have he := (div_eq_iff hβ.ne').mp hlog
  change Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + β * c
  rw [he]
  ring

/-- Existence and the a.e. Euler--Lagrange equation are actual conclusions for
every positive beta, through the preceding direct-method and variation chain. -/
theorem equilibrium_exists_minimizer_eulerLagrange_ae {β : ℝ} (hβ : 0 < β) :
    ∃ (μ : ProbabilityMeasure ℂ) (C : ℝ),
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      (∀ᵐ x : ℂ, 0 < equilibriumReferenceDensity μ x) ∧
      (∀ᵐ x : ℂ, Real.log (equilibriumReferenceDensity μ x) =
        -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential (equilibriumReferenceDensity μ) x) + C) ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, hfinite, hpos, hmin⟩ := equilibriumCanonical_exists_positive_minimizer hβ
  obtain ⟨C, hEL⟩ := equilibriumCanonicalMinimizer_eulerLagrange_ae hβ μ hfinite hmin
  exact ⟨μ, C, hfinite, hpos, hEL, hmin⟩

end RepulsiveCoulomb
