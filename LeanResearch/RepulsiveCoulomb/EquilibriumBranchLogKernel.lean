import LeanResearch.RepulsiveCoulomb.PlanarTruncatedLogKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Elementary analytic bounds for the literal planar Coulomb kernel.
The value at zero is the harmless real-log convention; later off-diagonal
energies and absolutely continuous reference measures do not use that value.
These are actual kernel estimates, not an assumed equilibrium construction. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The manuscript kernel `g(z) = -log |z|`. -/
def equilibriumLogKernel (z : ℂ) : ℝ := -Real.log ‖z‖

/-- Its nonnegative singular part. -/
def equilibriumLogPositive (z : ℂ) : ℝ := max (equilibriumLogKernel z) 0

/-- A one-body logarithmic moment weight. -/
def equilibriumLogMoment (z : ℂ) : ℝ := Real.log (1 + ‖z‖)

theorem equilibriumLogKernel_measurable : Measurable equilibriumLogKernel :=
  (Real.measurable_log.comp continuous_norm.measurable).neg

theorem equilibriumLogPositive_measurable : Measurable equilibriumLogPositive :=
  equilibriumLogKernel_measurable.max measurable_const

theorem equilibriumLogMoment_continuous : Continuous equilibriumLogMoment := by
  exact (continuous_const.add continuous_norm).log (fun z => by
    change 1 + ‖z‖ ≠ 0
    positivity)

theorem equilibriumLogMoment_nonneg (z : ℂ) : 0 ≤ equilibriumLogMoment z :=
  Real.log_nonneg (by have := norm_nonneg z; linarith)

theorem equilibriumLogMoment_le_norm (z : ℂ) : equilibriumLogMoment z ≤ ‖z‖ := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖z‖ by positivity)
  simpa [equilibriumLogMoment] using h

/-- Quadratic confinement absorbs the negative logarithmic tail with any
positive coefficient. The displayed constant is explicit. -/
theorem equilibriumLogMoment_le_quadratic {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    equilibriumLogMoment z ≤ δ * ‖z‖ ^ 2 + (4 * δ)⁻¹ := by
  have hsq := sq_nonneg (2 * δ * ‖z‖ - 1)
  have hden : 0 < 4 * δ := by positivity
  have hmul : (4 * δ) * ((4 * δ)⁻¹) = 1 := mul_inv_cancel₀ hden.ne'
  have hbound : ‖z‖ ≤ δ * ‖z‖ ^ 2 + (4 * δ)⁻¹ := by
    nlinarith
  exact (equilibriumLogMoment_le_norm z).trans hbound

/-- The elementary lower bound used in equilibrium coercivity and tails,
including the real-log value at a collision. -/
theorem equilibriumLogKernel_sub_lower (x y : ℂ) :
    -equilibriumLogMoment x - equilibriumLogMoment y ≤ equilibriumLogKernel (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, equilibriumLogKernel, norm_zero, Real.log_zero, neg_zero]
    have hx := equilibriumLogMoment_nonneg x
    linarith
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hbound : ‖x - y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
    have htri := norm_sub_le x y
    have hx := norm_nonneg x
    have hy := norm_nonneg y
    nlinarith [mul_nonneg hx hy]
  have hl := Real.log_le_log hn hbound
  rw [Real.log_mul (by positivity : 1 + ‖x‖ ≠ 0)
    (by positivity : 1 + ‖y‖ ≠ 0)] at hl
  unfold equilibriumLogKernel equilibriumLogMoment
  linarith

/-- An integrable pointwise majorant for the singular positive part. -/
theorem equilibriumLogPositive_le_truncatedForce (z : ℂ) :
    equilibriumLogPositive z ≤ truncatedLogKernel 1 z := by
  by_cases hz : z = 0
  · subst z
    norm_num [equilibriumLogPositive, equilibriumLogKernel, truncatedLogKernel]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h1 : ‖z‖ < 1
  · have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hn)
    rw [Real.log_inv] at hl
    unfold equilibriumLogPositive equilibriumLogKernel truncatedLogKernel
    rw [if_pos h1]
    exact max_le (by linarith) (inv_nonneg.mpr hn.le)
  · have hl := Real.log_nonneg (le_of_not_gt h1)
    simp only [equilibriumLogPositive, equilibriumLogKernel, truncatedLogKernel,
      if_neg h1]
    exact max_le (neg_nonpos.mpr hl) le_rfl

theorem equilibriumLogPositive_nonneg (z : ℂ) : 0 ≤ equilibriumLogPositive z :=
  le_max_right _ _

theorem equilibriumLogPositive_integrable : Integrable equilibriumLogPositive := by
  apply (truncatedLogKernel_integrable 1).mono'
    equilibriumLogPositive_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumLogPositive_nonneg z)]
    exact equilibriumLogPositive_le_truncatedForce z)

theorem equilibriumLogPositive_shift_integrable (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumLogPositive (x - y)) := by
  apply (equilibriumLogPositive_integrable.comp_sub_right x).congr
  exact Filter.Eventually.of_forall (fun y => by
    simp only [equilibriumLogPositive, equilibriumLogKernel, norm_sub_rev])

/-- Uniform, explicit local logarithmic mass bound. A sharper `pi / 2`
identity may replace this estimate later without changing its use. -/
theorem integral_equilibriumLogPositive_le :
    (∫ z : ℂ, equilibriumLogPositive z) ≤ 2 * Real.pi := by
  calc
    (∫ z : ℂ, equilibriumLogPositive z) ≤ ∫ z : ℂ, truncatedLogKernel 1 z :=
      integral_mono equilibriumLogPositive_integrable (truncatedLogKernel_integrable 1)
        equilibriumLogPositive_le_truncatedForce
    _ = 2 * Real.pi := by rw [integral_truncatedLogKernel (by norm_num)]; ring

theorem equilibriumLogKernel_abs_sub_bound (x y : ℂ) :
    |equilibriumLogKernel (x - y)| ≤ equilibriumLogPositive (x - y) +
      equilibriumLogMoment x + equilibriumLogMoment y := by
  have hlo := equilibriumLogKernel_sub_lower x y
  have hhi : equilibriumLogKernel (x - y) ≤ equilibriumLogPositive (x - y) := le_max_left _ _
  have hp := equilibriumLogPositive_nonneg (x - y)
  have hx := equilibriumLogMoment_nonneg x
  have hy := equilibriumLogMoment_nonneg y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RepulsiveCoulomb
