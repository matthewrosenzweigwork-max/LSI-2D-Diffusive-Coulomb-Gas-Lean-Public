module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCirclePotentialDifference

@[expose] public section

/-! Exact single-cutoff potential error for a bounded planar density. The
coefficient pi*epsilon^2/2 is retained, independently of the coarser all-p
moment estimate. This supplies the reference cross correction in Onsager. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumCircularPotential (ε : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y : ℂ, equilibriumCircularKernel ε (x - y) * ρ y

theorem equilibriumCircularPotential_difference {ε M : ℝ} (hε : 0 < ε)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρL : Integrable (fun y => equilibriumLogMoment y * ρ y)) (x : ℂ) :
    equilibriumDensityPotential ρ x - equilibriumCircularPotential ε ρ x =
      ∫ y : ℂ, equilibriumCircularError ε (y - x) * ρ y := by
  have hk := equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi hρL x
  have hE : Integrable (fun y : ℂ => equilibriumCircularError ε (y - x) * ρ y) := by
    simpa only [pow_one] using equilibriumCircularError_pow_mul_integrable hε 1 (by norm_num) hρm hρ0 hρM x
  have he : (fun y : ℂ => equilibriumLogKernel (x - y) * ρ y - equilibriumCircularError ε (y - x) * ρ y) =ᵐ[volume]
      (fun y : ℂ => equilibriumCircularKernel ε (x - y) * ρ y) := by
    filter_upwards [volume.ae_ne x] with y hy
    rw [← equilibriumCircularError_sub_symm ε x y,
      equilibriumCircularError_eq_sub hε (sub_ne_zero.mpr hy.symm)]
    ring
  unfold equilibriumDensityPotential equilibriumCircularPotential
  rw [← integral_congr_ae he, integral_sub hk hE]
  ring

/-- The exact sharp local error estimate under a density cap. -/
theorem equilibriumCircularError_integral_mul_sharp {ε M : ℝ} (hε : 0 < ε)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularError ε (y - x) * ρ y) ≤ M * Real.pi * ε ^ 2 / 2 := by
  have hi : Integrable (fun y : ℂ => equilibriumCircularError ε (y - x) * ρ y) := by
    simpa only [pow_one] using equilibriumCircularError_pow_mul_integrable hε 1 (by norm_num) hρm hρ0 hρM x
  have hmajor := ((equilibriumCircularError_integrable hε).comp_sub_right x).mul_const M
  have h := integral_mono hi hmajor (fun y =>
    mul_le_mul_of_nonneg_left (hρM y) (equilibriumCircularError_nonneg ε (y - x)))
  rw [integral_mul_const, integral_sub_right_eq_self, integral_equilibriumCircularError hε] at h
  nlinarith

/-- Actual two-sided cutoff-potential comparison, including every spatial point. -/
theorem equilibriumCircularPotential_bounds {ε M : ℝ} (hε : 0 < ε)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρL : Integrable (fun y => equilibriumLogMoment y * ρ y)) (x : ℂ) :
    equilibriumDensityPotential ρ x - M * Real.pi * ε ^ 2 / 2 ≤ equilibriumCircularPotential ε ρ x ∧
      equilibriumCircularPotential ε ρ x ≤ equilibriumDensityPotential ρ x := by
  have he := equilibriumCircularPotential_difference hε hρm hρ0 hρM hρi hρL x
  have hupper := equilibriumCircularError_integral_mul_sharp hε hρm hρ0 hρM x
  have hlower : (0 : ℝ) ≤ ∫ y : ℂ, equilibriumCircularError ε (y - x) * ρ y :=
    integral_nonneg (fun y => mul_nonneg (equilibriumCircularError_nonneg ε _) (hρ0 y))
  constructor <;> linarith

end RepulsiveCoulomb
