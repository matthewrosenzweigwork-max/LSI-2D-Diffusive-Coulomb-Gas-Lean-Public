import LeanResearch.RepulsiveCoulomb.CoulombHelmertCoordinates
import LeanResearch.RepulsiveCoulomb.CoulombCenterFormTransport

/-! Unconditional all-N measure factorization in the manuscript's explicit
Helmert coordinates. This closes the measure/metric assertion of prop:com;
the separate equality of optimal LSI rates is not asserted here. -/
noncomputable section
open MeasureTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

/-- The exact Helmert chart, with the center coordinate first. -/
def coulombCenterCoordinates (n : ℕ) : CoulombConfig (n + 1) ≃ᵐ ℂ × CoulombConfig n :=
  coulombCenterChart (coulombHelmertRotation n)

/-- The literal law of the N-1 relative Helmert coordinates. -/
def coulombCenterRelativeLaw (n : ℕ) (β : ℝ) : Measure (CoulombConfig n) :=
  (coulombMeasure (n + 1) β).map (fun z => (coulombCenterCoordinates n z).2)

theorem coulombCenterRelativeLaw_density (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombCenterRelativeLaw n β =
      coulombCenterRelativeMeasure (coulombHelmertRotation n) β :=
  coulombCenter_relative_marginal (coulombHelmertRotation n) (coulombHelmertRotation_axis n) hβ

/-- Exact product of the planar Gaussian and the actual relative-coordinate law. -/
theorem coulombCenter_factorization (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMeasure (n + 1) β).map (coulombCenterCoordinates n) =
      (coulombCenterGaussian β).prod (coulombCenterRelativeLaw n β) := by
  rw [coulombCenterRelativeLaw_density n hβ]
  exact coulombCenter_joint_law (coulombHelmertRotation n) (coulombHelmertRotation_axis n) hβ

/-- The Gaussian factor is exactly β/(2π) exp(-β |c|²/2) dc. -/
theorem coulombCenter_factorization_explicit (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMeasure (n + 1) β).map (coulombCenterCoordinates n) =
      (volume.withDensity (fun c : ℂ =>
        ENNReal.ofReal ((β / (2 * Real.pi)) * Real.exp (-β * ‖c‖ ^ 2 / 2)))).prod
          (coulombCenterRelativeLaw n β) := by
  rw [coulombCenter_factorization n hβ, coulombCenterGaussian_density hβ]

/-- Extended entropy factorization on every element of the original full form. -/
theorem coulombCenter_full_form_entropy (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (n + 1) hβ) :
    entropy (coulombMeasure (n + 1) β)
      (fun z => (coulombFormValueL (n + 1) hβ u z) ^ 2) =
      entropy ((coulombCenterGaussian β).prod (coulombCenterRelativeLaw n β))
        (fun p => coulombCenterFormValue (coulombHelmertRotation n) hβ u p ^ 2) := by
  rw [coulombCenterRelativeLaw_density n hβ]
  exact coulombCenterForm_entropy (coulombHelmertRotation n) (coulombHelmertRotation_axis n) hβ u

end RepulsiveCoulomb
