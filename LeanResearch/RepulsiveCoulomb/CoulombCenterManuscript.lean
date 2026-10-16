module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeCommonCore
public import LeanResearch.RepulsiveCoulomb.CoulombCenterRealOptimalFactorization

@[expose] public section

/-! Complete source-facing center-of-mass proposition: literal Helmert
factorization, relative common-core domain identification, and equality of the
ACTUAL REAL optimal LSI rates on the original and full relative forms. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

/-- Manuscript prop:com, with its relative-domain identification included
explicitly rather than left to an unexported side argument. N=m+2 ranges over
all manuscript particle numbers. -/
theorem coulomb_center_mass_manuscript (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    ((coulombMeasure (m + 2) β).map (coulombCenterCoordinates (m + 1)) =
      (volume.withDensity (fun c : ℂ =>
        ENNReal.ofReal ((β / (2 * Real.pi)) * Real.exp (-β * ‖c‖ ^ 2 / 2)))).prod
          (coulombCenterRelativeLaw (m + 1) β)) ∧
    (closure (range (coulombCenterRelativeAmbientJet (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ)) =
      (coulombCenterRelativeFormSubmodule (coulombHelmertRotation (m + 1))
        (coulombHelmertRotation_axis (m + 1)) hβ : Set _)) ∧
    poleBranchOptimalLSIRate (m + 2) hβ =
      min β (coulombHelmertRelativeOptimalLSIRateReal m hβ) :=
  ⟨coulombCenter_factorization_explicit (m + 1) hβ,
    coulombCenter_relative_common_core m (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ,
    coulomb_center_mass_optimal_lsi_rate_real_min m hβ⟩

/-- Exact arbitrary-N real optimum formulation, retaining the manuscript's
explicit N≥2 hypothesis. -/
theorem coulomb_center_mass_optimal_lsi_rate_all_N (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate N hβ =
      min β (coulombHelmertRelativeOptimalLSIRateReal (N - 2) hβ) := by
  simpa only [Nat.sub_add_cancel hN] using
    coulomb_center_mass_optimal_lsi_rate_real_min (N - 2) hβ

end RepulsiveCoulomb
