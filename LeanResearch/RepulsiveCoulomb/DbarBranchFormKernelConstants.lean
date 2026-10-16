module

public import LeanResearch.RepulsiveCoulomb.DbarBranchRealKernel
public import LeanResearch.RepulsiveCoulomb.PoleBranchCollisionConnectedness

@[expose] public section

/-! Every actual zero-energy full-form value is almost everywhere constant,
for all N and β > 0. The argument uses domain connectedness and weak-kernel
regularity. These records-only dependencies and this module remain uncompiled. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem coulombForm_zero_gradient_constant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (hu : coulombFormGradientL N hβ u = 0) :
    ∃ a : ℝ, coulombFormValueL N hβ u =ᵐ[coulombMeasure N β] fun _ => a :=
  coulombForm_zero_gradient_constant_of_connected hβ
    (poleBranch_coulombDomain_isPreconnected N) u hu

theorem coulombForm_zero_energy_constant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (hu : coulombFormEnergy N hβ u = 0) :
    ∃ a : ℝ, coulombFormValueL N hβ u =ᵐ[coulombMeasure N β] fun _ => a := by
  apply coulombForm_zero_gradient_constant hβ u
  by_contra hn
  have hp : 0 < ‖coulombFormGradientL N hβ u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  change ‖coulombFormGradientL N hβ u‖ ^ 2 = 0 at hu
  linarith

end RepulsiveCoulomb
