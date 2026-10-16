module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSmoothedDensity
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceCompactBounds

@[expose] public section

/-! Circle smoothing preserves every real nonnegative polynomial moment of
the actual thermal reference. The bound is (1+epsilon)^m times the original
moment, and P2 follows as actual integrability of the smoothed density law. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
namespace RepulsiveCoulomb

theorem equilibriumPolynomialWeight_add_le {m : ℝ} (hm : 0 ≤ m) (x y : ℂ) :
    (1 + ‖x + y‖) ^ m ≤ (1 + ‖x‖) ^ m * (1 + ‖y‖) ^ m := by
  have hn : 1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
    nlinarith [norm_add_le x y, norm_nonneg x, norm_nonneg y]
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖x + y‖) hn hm
  rwa [Real.mul_rpow (by positivity : 0 ≤ 1 + ‖x‖) (by positivity : 0 ≤ 1 + ‖y‖)] at h

theorem equilibriumCircle_polynomialMoment {ε m : ℝ} (hε : 0 ≤ ε) (hm : 0 ≤ m) :
    Integrable (fun z : ℂ => (1 + ‖z‖) ^ m) (equilibriumCircleMeasure 0 ε) ∧
      (∫ z : ℂ, (1 + ‖z‖) ^ m ∂equilibriumCircleMeasure 0 ε) = (1 + ε) ^ m := by
  have hc : Continuous (fun z : ℂ => (1 + ‖z‖) ^ m) :=
    (Real.continuous_rpow_const hm).comp (continuous_const.add continuous_norm)
  refine ⟨integrable_equilibriumCircleMeasure_of_circleIntegrable 0 ε hc.measurable
    hc.continuousOn.circleIntegrable', ?_⟩
  apply integral_eq_const
  have hs : ∀ᵐ z ∂equilibriumCircleMeasure 0 ε, z ∈ sphere (0 : ℂ) ε :=
    mem_ae_iff.mpr (equilibriumCircleMeasure_supported 0 hε)
  filter_upwards [hs] with z hz
  have hn : ‖z‖ = ε := by simpa only [dist_zero_right] using Metric.mem_sphere.mp hz
  rw [hn]

/-- Actual integrability and quantitative moment transfer through circle
convolution. The original reference is not silently reused in a cross term. -/
theorem equilibriumReference_smoothed_polynomialMoment {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε m : ℝ} (hε : 0 ≤ ε) (hm : 0 ≤ m) :
    Integrable (fun x : ℂ => (1 + ‖x‖) ^ m)
      (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) ∧
    (∫ x : ℂ, (1 + ‖x‖) ^ m ∂equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) ≤
      (1 + ε) ^ m * (∫ y : ℂ, (1 + ‖y‖) ^ m ∂R.measure) := by
  let w : ℂ → ℝ := fun x => (1 + ‖x‖) ^ m
  have hwm : Measurable w :=
    ((Real.continuous_rpow_const hm).comp (continuous_const.add continuous_norm)).measurable
  have hw0 (x : ℂ) : 0 ≤ w x := Real.rpow_nonneg (by positivity) _
  obtain ⟨hc, hci⟩ := equilibriumCircle_polynomialMoment hε hm
  have hμ := (equilibriumReference_polynomial_moment_bound hβ le_rfl le_rfl hm R).1
  have hmajor := hc.mul_prod hμ
  have hF : Integrable (fun p : ℂ × ℂ => w (p.1 + p.2))
      ((equilibriumCircleMeasure 0 ε).prod R.measure) := by
    apply hmajor.mono' (hwm.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖w (p.1 + p.2)‖ ≤ (1 + ‖p.1‖) ^ m * (1 + ‖p.2‖) ^ m
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
      exact equilibriumPolynomialWeight_add_le hm p.1 p.2)
  have hconv : Integrable w ((equilibriumCircleMeasure 0 ε).conv (R.measure : Measure ℂ)) := by
    change Integrable w (Measure.map (fun p : ℂ × ℂ => p.1 + p.2)
      ((equilibriumCircleMeasure 0 ε).prod (R.measure : Measure ℂ)))
    exact (integrable_map_measure hwm.aestronglyMeasurable
      (measurable_fst.add measurable_snd).aemeasurable).mpr hF
  rw [equilibriumReference_smoothed_measure R ε]
  refine ⟨hconv, ?_⟩
  rw [integral_conv hconv]
  have h := integral_mono hF hmajor (fun p => equilibriumPolynomialWeight_add_le hm p.1 p.2)
  rw [integral_prod _ hF, integral_prod_mul (fun z : ℂ => (1 + ‖z‖) ^ m)
    (fun y : ℂ => (1 + ‖y‖) ^ m), hci] at h
  exact h

/-- The actual smoothed reference remains P2; no energy or moment property of
a newly introduced reference is left as an unproved hypothesis. -/
theorem equilibriumReference_smoothed_secondMoment_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2)
      (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) := by
  have h := (equilibriumReference_smoothed_polynomialMoment hβ R hε (by norm_num : (0 : ℝ) ≤ 2)).1
  apply h.mono' (by fun_prop)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖), Real.rpow_two]
    nlinarith [norm_nonneg x])

/-- Literal weighted density integrability for the smoothed P2 law. -/
theorem equilibriumReference_smoothed_density_secondMoment {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumSmoothedDensity ε R.density x) := by
  have h := (equilibriumDensityMeasure_integrable_iff
    (equilibriumSmoothedDensity_measurable ε R.smooth.continuous.measurable)
    (equilibriumSmoothedDensity_nonneg ε (fun x => (R.positive x).le))
    (fun x : ℂ => ‖x‖ ^ 2)).mp (equilibriumReference_smoothed_secondMoment_integrable hβ R hε)
  simpa only [mul_comm] using h

end RepulsiveCoulomb
