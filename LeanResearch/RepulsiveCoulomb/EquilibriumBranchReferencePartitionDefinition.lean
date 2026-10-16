import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedDefinition
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference

/-! The literal partition integral, independent of its later estimates. -/
noncomputable section
open MeasureTheory
namespace RepulsiveCoulomb

def equilibriumReferencePartition {β : ℝ} (N : ℕ) (t : ℝ)
    (R : EquilibriumConstructedReference β) : ℝ :=
  ∫ z : Fin N → ℂ, Real.exp (-t * equilibriumModulatedEnergy R.density z)
    ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))

end RepulsiveCoulomb
