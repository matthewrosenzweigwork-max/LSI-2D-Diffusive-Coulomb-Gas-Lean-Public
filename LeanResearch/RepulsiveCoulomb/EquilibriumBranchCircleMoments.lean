import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEnergy
import Mathlib.Analysis.Complex.MeanValue

/-! Exact affine and quadratic moments of the actual normalized circular
measure. The quadratic increment is epsilon^2, which fixes the one-half
confinement contribution in the sharp density-cap argument. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
namespace RepulsiveCoulomb

theorem integral_equilibriumCircleMeasure_re (c : ℂ) (r : ℝ) :
    (∫ z : ℂ, z.re ∂equilibriumCircleMeasure c r) = c.re := by
  rw [integral_equilibriumCircleMeasure c r Complex.continuous_re.measurable]
  have hid : Real.circleAverage (fun z : ℂ => z) c r = c :=
    (Differentiable.diffContOnCl differentiable_id).circleAverage
  have h := Complex.reCLM.circleAverage_comp_comm
    (show CircleIntegrable (fun z : ℂ => z) c r from continuous_id.continuousOn.circleIntegrable')
  simpa only [Function.comp_def, Complex.reCLM_apply, hid] using h

theorem integral_equilibriumCircleMeasure_im (c : ℂ) (r : ℝ) :
    (∫ z : ℂ, z.im ∂equilibriumCircleMeasure c r) = c.im := by
  rw [integral_equilibriumCircleMeasure c r Complex.continuous_im.measurable]
  have hid : Real.circleAverage (fun z : ℂ => z) c r = c :=
    (Differentiable.diffContOnCl differentiable_id).circleAverage
  have h := Complex.imCLM.circleAverage_comp_comm
    (show CircleIntegrable (fun z : ℂ => z) c r from continuous_id.continuousOn.circleIntegrable')
  simpa only [Function.comp_def, Complex.imCLM_apply, hid] using h

/-- Exact quadratic moment with the actual normalized circle law. -/
theorem integral_equilibriumCircleMeasure_norm_sq (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ z : ℂ, ‖z‖ ^ 2 ∂equilibriumCircleMeasure c r) = ‖c‖ ^ 2 + r ^ 2 := by
  have hire : Integrable (fun z : ℂ => z.re) (equilibriumCircleMeasure c r) :=
    integrable_equilibriumCircleMeasure_of_circleIntegrable c r Complex.continuous_re.measurable
      Complex.continuous_re.continuousOn.circleIntegrable'
  have hiim : Integrable (fun z : ℂ => z.im) (equilibriumCircleMeasure c r) :=
    integrable_equilibriumCircleMeasure_of_circleIntegrable c r Complex.continuous_im.measurable
      Complex.continuous_im.continuousOn.circleIntegrable'
  have hs : ∀ᵐ z ∂equilibriumCircleMeasure c r, z ∈ sphere c r :=
    mem_ae_iff.mpr (equilibriumCircleMeasure_supported c hr)
  have he : (fun z : ℂ => ‖z‖ ^ 2) =ᵐ[equilibriumCircleMeasure c r]
      (fun z => (r ^ 2 - ‖c‖ ^ 2) + 2 * (c.re * z.re + c.im * z.im)) := by
    filter_upwards [hs] with z hz
    have hn : ‖z - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hn2 := congrArg (fun t : ℝ => t ^ 2) hn
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hn2 ⊢
    nlinarith
  rw [integral_congr_ae he]
  have ha := integral_add (integrable_const (μ := equilibriumCircleMeasure c r) (r ^ 2 - ‖c‖ ^ 2))
    (((hire.const_mul c.re).add (hiim.const_mul c.im)).const_mul 2)
  have hb := integral_add (hire.const_mul c.re) (hiim.const_mul c.im)
  dsimp only [Pi.add_apply] at ha hb
  rw [ha, integral_const_mul, hb, integral_const_mul, integral_const_mul,
    integral_equilibriumCircleMeasure_re, integral_equilibriumCircleMeasure_im]
  simp only [integral_const, probReal_univ, one_smul, Complex.sq_norm, Complex.normSq_apply]
  ring

end RepulsiveCoulomb
