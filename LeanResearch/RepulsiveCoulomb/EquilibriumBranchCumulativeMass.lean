import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonOrigin
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Cumulative ball mass for an actual planar reference. Absolute continuity
makes every sphere null, so dominated convergence proves continuity without
assuming density continuity. A bounded density gives the exact M*pi*r^2
bound needed at the origin of the Newton gradient. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def equilibriumCumulativeMass (μ : Measure ℂ) (r : ℝ) : ℝ := μ.real (ball 0 r)

theorem equilibriumCumulativeMass_nonneg (μ : Measure ℂ) (r : ℝ) :
    0 ≤ equilibriumCumulativeMass μ r := measureReal_nonneg

/-- Sphere-nullity proves continuity of the radial cumulative mass. -/
theorem equilibriumCumulativeMass_continuous {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hAC : μ ≪ volume) : Continuous (equilibriumCumulativeMass μ) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  let F : ℝ → ℂ → ℝ := fun t y => (ball (0 : ℂ) t).indicator (fun _ => 1) y
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) μ :=
    (measurable_const.indicator measurableSet_ball).aestronglyMeasurable
  have hFb (t : ℝ) (y : ℂ) : ‖F t y‖ ≤ 1 := by
    by_cases hy : y ∈ ball (0 : ℂ) t
    · simp only [F, Set.indicator_of_mem hy, norm_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hy, norm_zero, zero_le_one]
  have hs : μ (sphere (0 : ℂ) r) = 0 := hAC (equilibriumCircle_support_volume_zero 0 r)
  have hct : ∀ᵐ y ∂μ, ContinuousAt (fun t : ℝ => F t y) r := by
    filter_upwards [compl_mem_ae_iff.mpr hs] with y hy
    have hne : ‖y‖ ≠ r := by simpa only [Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) r).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hlt] with t ht
      have hym : y ∈ ball (0 : ℂ) t := by simpa only [Metric.mem_ball, dist_zero_right, Set.mem_Ioi] using ht
      exact Set.indicator_of_mem hym _
    · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hgt] with t ht
      have hym : y ∉ ball (0 : ℂ) t := by
        simp only [Metric.mem_ball, dist_zero_right, not_lt]
        exact ht.le
      exact Set.indicator_of_notMem hym _
  have hc := continuousAt_of_dominated (F := F) (bound := fun _ => (1 : ℝ))
    (Eventually.of_forall hFm) (Eventually.of_forall (fun t => Eventually.of_forall (hFb t)))
    (integrable_const (μ := μ) (1 : ℝ)) hct
  have he : (fun t : ℝ => ∫ y : ℂ, F t y ∂μ) = equilibriumCumulativeMass μ := by
    funext t
    simp only [F, integral_indicator_const (1 : ℝ) measurableSet_ball, smul_eq_mul, mul_one,
      equilibriumCumulativeMass]
  rwa [he] at hc

/-- The literal density law is dominated by M times planar volume. -/
theorem equilibriumDensityMeasure_le_volume {ρ : ℂ → ℝ} {M : ℝ} (hρM : ∀ y, ρ y ≤ M) :
    equilibriumDensityMeasure ρ ≤ ENNReal.ofReal M • (volume : Measure ℂ) := by
  unfold equilibriumDensityMeasure
  rw [← withDensity_const]
  exact withDensity_mono (Eventually.of_forall (fun y => ENNReal.ofReal_le_ofReal (hρM y)))

/-- Exact cumulative-mass bound; the factor pi is the actual planar ball volume. -/
theorem equilibriumCumulativeMass_density_bound {ρ : ℂ → ℝ} {M r : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M) (hr : 0 ≤ r) :
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r ≤ M * Real.pi * r ^ 2 := by
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have he := equilibriumDensityMeasure_le_volume hρM (ball (0 : ℂ) r)
  have hfin : (ENNReal.ofReal M • (volume : Measure ℂ)) (ball 0 r) ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul, Complex.volume_ball]
    finiteness
  have ht := ENNReal.toReal_mono hfin he
  change equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r ≤ _ at ht
  rw [Measure.smul_apply, smul_eq_mul, Complex.volume_ball, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hM, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi] at ht
  nlinarith

end RepulsiveCoulomb
