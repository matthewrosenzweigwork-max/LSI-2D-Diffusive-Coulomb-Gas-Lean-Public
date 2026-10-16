import LeanResearch.RepulsiveCoulomb.EquilibriumBranchInteraction
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedCentering

/-! Exact canonical energy and measurability, separated from its later
Onsager estimate. Records-only refactor after the 2026-10-01 recovery. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Literal A_N from the canonical manuscript, with its full one-body term. -/
def equilibriumModulatedEnergy {N : ℕ} (ρ : ℂ → ℝ) (z : Fin N → ℂ) : ℝ :=
  equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) / (2 * (N : ℝ)) -
    (∑ i, equilibriumDensityPotential ρ (z i)) + (N : ℝ) * equilibriumDensityInteraction ρ / 2

theorem equilibriumModulatedEnergy_measurable {N : ℕ} {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measurable (equilibriumModulatedEnergy (N := N) ρ) := by
  have hp (i j : Fin N) : Measurable (fun z : Fin N → ℂ =>
      if i = j then (0 : ℝ) else equilibriumLogKernel (z i - z j)) := by
    by_cases hij : i = j
    · simp only [hij, if_true]
      exact measurable_const
    · simp only [hij, if_false]
      exact equilibriumLogKernel_measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have hsum := Finset.measurable_sum Finset.univ (fun i _ =>
    Finset.measurable_sum Finset.univ (fun j _ => hp i j))
  have hu : Measurable (fun z : Fin N → ℂ => ∑ i, equilibriumDensityPotential ρ (z i)) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      (equilibriumDensityPotential_measurable hρm).comp (measurable_pi_apply i))
  exact ((hsum.div_const _).sub hu).add measurable_const

end RepulsiveCoulomb
