import LeanResearch.RepulsiveCoulomb.CoulombCenterManuscript

/-! Complete source-facing center-of-mass proposition: literal Helmert
factorization, relative common-core domain identification, and equality of the
ACTUAL REAL optimal LSI rates on the original and full relative forms. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- Manuscript prop:com, with its relative-domain identification included
explicitly rather than left to an unexported side argument. N=m+2 ranges over
all manuscript particle numbers. -/
theorem paper_original_center_mass (m : ℕ) {β : ℝ} (hβ : 0 < β) :
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
  coulomb_center_mass_manuscript m hβ

/-- Exact arbitrary-N real optimum formulation, retaining the manuscript's
explicit N≥2 hypothesis. -/
theorem paper_original_center_mass_optimal_rate (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate N hβ =
      min β (coulombHelmertRelativeOptimalLSIRateReal (N - 2) hβ) :=
  coulomb_center_mass_optimal_lsi_rate_all_N N hN hβ

/-- Literal normalized center and relative Helmert rows, with the original sign. -/
theorem paper_original_helmert_center (n : ℕ) (z : CoulombConfig (n + 1)) :
    coulombHelmertEquiv n z 0 =
      ((Real.sqrt (n + 1 : ℝ))⁻¹ : ℂ) * ∑ j, z j :=
  coulombHelmertEquiv_zero n z

theorem paper_original_helmert_relative (n : ℕ) (z : CoulombConfig (n + 1)) (k : Fin n) :
    coulombHelmertEquiv n z k.succ =
      ((Real.sqrt (((k.val : ℝ) + 1) * ((k.val : ℝ) + 2)))⁻¹ : ℂ) *
        ((∑ j ∈ Finset.Iio k.succ, z j) - ((k.val : ℂ) + 1) * z k.succ) :=
  coulombHelmertEquiv_succ n z k

theorem paper_original_helmert_unitary (n : ℕ) (z w : CoulombConfig (n + 1)) :
    inner ℂ (coulombHelmertEquiv n z) (coulombHelmertEquiv n w) = inner ℂ z w :=
  coulombHelmertEquiv_inner n z w

end RepulsiveCoulomb.PaperRoute
