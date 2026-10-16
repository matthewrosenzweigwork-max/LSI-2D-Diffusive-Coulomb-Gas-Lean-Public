import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyLower

/-! The negative entropy part is actually integrable on the entire absolutely
continuous P2 domain. The positive part may be infinite. This is a prerequisite
for an extended free-energy correspondence, not a finite-entropy restriction. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

def equilibriumEntropyNegative (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  max (-(ρ x * Real.log (ρ x))) 0

theorem equilibriumEntropyNegative_nonneg (ρ : ℂ → ℝ) (x : ℂ) :
    0 ≤ equilibriumEntropyNegative ρ x := le_max_right _ _

theorem equilibriumEntropyNegative_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measurable (equilibriumEntropyNegative ρ) :=
  (hρm.mul (Real.measurable_log.comp hρm)).neg.max measurable_const

/-- A Gaussian lower bound controls only the negative entropy part; it does
not postulate finite positive entropy. -/
theorem equilibriumEntropyNegative_bound {a : ℝ} (ha : 0 < a)
    {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (x : ℂ) :
    equilibriumEntropyNegative ρ x ≤ a * (‖x‖ ^ 2 * ρ x) +
      (|Real.log (a / Real.pi)| + 1) * ρ x + equilibriumGaussian a x := by
  have hl := equilibrium_mul_log_lower (hρ0 x) (equilibriumGaussian_pos ha x)
  rw [log_equilibriumGaussian ha] at hl
  have hb := neg_le_abs (Real.log (a / Real.pi))
  have hm := mul_le_mul_of_nonneg_right hb (hρ0 x)
  have hg := (equilibriumGaussian_pos ha x).le
  have hr := mul_nonneg ha.le (mul_nonneg (sq_nonneg ‖x‖) (hρ0 x))
  have hc := mul_nonneg (show 0 ≤ |Real.log (a / Real.pi)| + 1 by positivity) (hρ0 x)
  unfold equilibriumEntropyNegative
  apply max_le
  · nlinarith [hρ0 x]
  · linarith

/-- Full P2 density statement: only measurability, nonnegativity, finite mass
and second moment are needed. Normalization and L-infinity are unnecessary. -/
theorem equilibriumEntropyNegative_integrable {a : ℝ} (ha : 0 < a) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    Integrable (equilibriumEntropyNegative ρ) := by
  have hmajor := ((hρ2.const_mul a).add
    (hρi.const_mul (|Real.log (a / Real.pi)| + 1))).add (equilibriumGaussian_integrable ha)
  apply hmajor.mono' (equilibriumEntropyNegative_measurable hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumEntropyNegative_nonneg ρ x)]
    exact equilibriumEntropyNegative_bound ha hρ0 x)

end RepulsiveCoulomb
