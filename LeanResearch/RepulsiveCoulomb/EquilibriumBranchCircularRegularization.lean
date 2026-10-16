import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogMass
import LeanResearch.RepulsiveCoulomb.PointWeightCircle

/-! Actual circular regularization of the planar logarithmic kernel and its
quantitative L1 error. This is a genuine small-scale input for the partition
argument. No positive-definiteness claim is made for one circular smearing. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The circle-smeared logarithmic kernel at radius epsilon. -/
def equilibriumCircularKernel (ε : ℝ) (z : ℂ) : ℝ := -Real.log (max ε ‖z‖)

/-- Its nonnegative off-diagonal regularization error. -/
def equilibriumCircularError (ε : ℝ) (z : ℂ) : ℝ :=
  equilibriumLogPositive (ε⁻¹ • z)

theorem equilibriumCircularKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (equilibriumCircularKernel ε) := by
  exact ((continuous_const.max continuous_norm).log (fun z => by
    change max ε ‖z‖ ≠ 0
    exact ne_of_gt (hε.trans_le (le_max_left _ _)))).neg

theorem equilibriumCircularKernel_eq_log_posLog {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    equilibriumCircularKernel ε z = -Real.log ε - Real.posLog (ε⁻¹ * ‖z‖) := by
  have hscale : 0 ≤ ε⁻¹ * ‖z‖ := mul_nonneg (inv_nonneg.mpr hε.le) (norm_nonneg _)
  by_cases hz : ‖z‖ ≤ ε
  · have hs : ε⁻¹ * ‖z‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hε]
      simpa using hz
    rw [equilibriumCircularKernel, max_eq_left hz,
      (Real.posLog_eq_zero_iff _).mpr (by rwa [abs_of_nonneg hscale]), sub_zero]
  · have hn : 0 < ‖z‖ := hε.trans (lt_of_not_ge hz)
    have hs : 1 ≤ ε⁻¹ * ‖z‖ := by
      rw [le_inv_mul_iff₀ hε]
      simpa using (le_of_lt (lt_of_not_ge hz))
    rw [equilibriumCircularKernel, max_eq_right (le_of_lt (lt_of_not_ge hz)),
      Real.posLog_eq_log (by rwa [abs_of_nonneg hscale]),
      Real.log_mul (inv_ne_zero hε.ne') hn.ne', Real.log_inv]
    ring

/-- The truncation is exactly the actual circle average, not a formal proxy. -/
theorem equilibriumCircularKernel_eq_circleAverage {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumCircularKernel ε (x - y) =
      Real.circleAverage (fun z : ℂ => equilibriumLogKernel (z - y)) x ε := by
  have hneg : Real.circleAverage (fun z : ℂ => equilibriumLogKernel (z - y)) x ε =
      -Real.circleAverage (fun z : ℂ => Real.log ‖z - y‖) x ε := by
    have h := Real.circleAverage_fun_smul (a := (-1 : ℝ))
      (f := fun z : ℂ => Real.log ‖z - y‖) (c := x) (R := ε)
    simpa only [equilibriumLogKernel, smul_eq_mul, neg_one_mul] using h
  rw [hneg, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hε.ne',
    equilibriumCircularKernel_eq_log_posLog hε]
  ring

theorem equilibriumCircularError_nonneg (ε : ℝ) (z : ℂ) :
    0 ≤ equilibriumCircularError ε z := equilibriumLogPositive_nonneg _

theorem equilibriumCircularError_measurable (ε : ℝ) :
    Measurable (equilibriumCircularError ε) :=
  equilibriumLogPositive_measurable.comp (continuous_const_smul ε⁻¹).measurable

/-- Off the omitted empirical diagonal, the error is exactly g-g_epsilon. -/
theorem equilibriumCircularError_eq_sub {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : z ≠ 0) :
    equilibriumCircularError ε z = equilibriumLogKernel z - equilibriumCircularKernel ε z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hs : 0 < ε⁻¹ * ‖z‖ := mul_pos (inv_pos.mpr hε) hn
  have hl : Real.log (ε⁻¹ * ‖z‖) = -Real.log ε + Real.log ‖z‖ := by
    rw [Real.log_mul (inv_ne_zero hε.ne') hn.ne', Real.log_inv]
  rw [equilibriumCircularError, equilibriumLogPositive, equilibriumLogKernel,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), hl,
    equilibriumCircularKernel_eq_log_posLog hε, Real.posLog_apply, hl]
  unfold equilibriumLogKernel
  by_cases h : 0 ≤ -Real.log ε + Real.log ‖z‖
  · rw [max_eq_right (by linarith), max_eq_right h]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (le_of_not_ge h)]
    ring

theorem equilibriumCircularKernel_le_logKernel {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z ≠ 0) : equilibriumCircularKernel ε z ≤ equilibriumLogKernel z := by
  have h := equilibriumCircularError_nonneg ε z
  rw [equilibriumCircularError_eq_sub hε hz] at h
  linarith

theorem equilibriumCircularError_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (equilibriumCircularError ε) :=
  equilibriumLogPositive_integrable.comp_smul (inv_ne_zero hε.ne')

/-- Exact scale-epsilon L1 error, with the manuscript's planar normalization. -/
theorem integral_equilibriumCircularError {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℂ, equilibriumCircularError ε z) = Real.pi * ε ^ 2 / 2 := by
  unfold equilibriumCircularError
  rw [Measure.integral_comp_inv_smul (volume : Measure ℂ),
    integral_equilibriumLogPositive]
  simp only [Complex.finrank_real_complex, smul_eq_mul, abs_of_nonneg (sq_nonneg ε)]
  ring

/-- The literal kernel difference has this same finite L1 mass; the value at
zero is handled by Lebesgue nullity rather than silently changed. -/
theorem equilibriumCircularDifference_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z : ℂ => equilibriumLogKernel z - equilibriumCircularKernel ε z) := by
  apply (equilibriumCircularError_integrable hε).congr
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  exact equilibriumCircularError_eq_sub hε hz

end RepulsiveCoulomb
