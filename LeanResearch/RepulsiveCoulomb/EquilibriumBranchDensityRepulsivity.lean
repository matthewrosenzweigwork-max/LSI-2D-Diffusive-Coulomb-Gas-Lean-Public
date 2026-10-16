import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogPositivity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCrossInteraction

/-! Actual application of logarithmic repulsivity to bounded probability
densities. The finite absolute-energy input is proved by CrossInteraction,
not supplied as a new assumption. This is the interaction-convexity input
for thermal-equilibrium uniqueness. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

theorem equilibriumDensityDifference_repulsive {ρ σ : ℂ → ℝ} {Mρ Mσ : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ Mρ)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσM : ∀ x, σ x ≤ Mσ)
    (hσi : Integrable σ) (hσmass : (∫ x : ℂ, σ x) = 1)
    (hσL : Integrable (fun x : ℂ => equilibriumLogMoment x * σ x)) :
    0 ≤ ∫ p : ℂ × ℂ, (ρ p.1 - σ p.1) * (ρ p.2 - σ p.2) *
      equilibriumLogKernel (p.1 - p.2) ∂volume.prod volume := by
  have h0 : (∫ x : ℂ, ρ x - σ x) = 0 := by
    rw [integral_sub hρi hσi, hρmass, hσmass, sub_self]
  exact equilibriumLogKernel_zeroMass_nonneg (hρm.sub hσm) (hρi.sub hσi) h0
    (equilibriumDifference_logEnergy_integrable hρm hρ0 hρM hρi hρmass hρL
      hσm hσ0 hσM hσi hσmass hσL)

end RepulsiveCoulomb
