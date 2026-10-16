module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonC1
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRadialAverageSmooth

@[expose] public section

/-! Actual radial mass formula with exact planar factor 2*pi. The radial
average is J(x)=integral_0^1 s*rho(s*x)ds, so enclosed mass is
2*pi*|x|^2*J(x). No square-root substitution or negative-radius extension is
required. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem equilibriumDensityMeasure_real_ball {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (r : ℝ) :
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r = ∫ y in ball (0 : ℂ) r, ρ y := by
  have hi := integral_equilibriumDensityMeasure hρm hρ0
    ((ball (0 : ℂ) r).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const 1 measurableSet_ball] at hi
  simp only [smul_eq_mul, mul_one] at hi
  change (equilibriumDensityMeasure ρ).real (ball 0 r) = _
  rw [hi, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    by_cases hy : y ∈ ball (0 : ℂ) r
    · simp only [Set.indicator_of_mem hy, mul_one]
    · simp only [Set.indicator_of_notMem hy, mul_zero])

/-- The actual planar norm-integration theorem supplies the factor 2*pi. -/
theorem equilibriumCumulativeMass_radial_profile {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    {r : ℝ} (hr : 0 ≤ r) :
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r =
      2 * Real.pi * ∫ t in (0 : ℝ)..r, t * ρ (t : ℂ) := by
  let f : ℝ → ℝ := (Iio r).indicator (fun t => ρ (t : ℂ))
  have hprofile (y : ℂ) : ρ y = ρ (‖y‖ : ℂ) := by
    apply hρrad
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
  have he : (ball (0 : ℂ) r).indicator ρ = (fun y : ℂ => f ‖y‖) := by
    funext y
    by_cases hy : ‖y‖ < r
    · have hyb : y ∈ ball (0 : ℂ) r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
      have hyi : ‖y‖ ∈ Iio r := hy
      simp only [f, Set.indicator_of_mem hyb, Set.indicator_of_mem hyi, hprofile y]
    · have hyb : y ∉ ball (0 : ℂ) r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
      have hyi : ‖y‖ ∉ Iio r := hy
      simp only [f, Set.indicator_of_notMem hyb, Set.indicator_of_notMem hyi]
  rw [equilibriumDensityMeasure_real_ball hρm hρ0, ← integral_indicator measurableSet_ball, he,
    integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f]
  have hinner : (∫ t in Ioi (0 : ℝ), t ^ (Module.finrank ℝ ℂ - 1) • f t) =
      ∫ t in (0 : ℝ)..r, t * ρ (t : ℂ) := by
    have hf : (fun t : ℝ => t ^ (Module.finrank ℝ ℂ - 1) • f t) =
        (Iio r).indicator (fun t : ℝ => t * ρ (t : ℂ)) := by
      funext t
      by_cases ht : t ∈ Iio r
      · simp only [f, Complex.finrank_real_complex, show 2 - 1 = 1 by norm_num,
          pow_one, smul_eq_mul, Set.indicator_of_mem ht]
      · simp only [f, Complex.finrank_real_complex, show 2 - 1 = 1 by norm_num,
          pow_one, smul_eq_mul, Set.indicator_of_notMem ht, mul_zero]
    rw [hf, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr]
  rw [hinner]
  simp [Measure.real, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Enclosed mass equals the exact Cartesian radial average at every point. -/
theorem equilibriumCumulativeMass_eq_radialAverage {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) (x : ℂ) :
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) ‖x‖ =
      2 * Real.pi * ‖x‖ ^ 2 * equilibriumRadialAverage ρ x := by
  rw [equilibriumCumulativeMass_radial_profile hρm hρ0 hρrad (norm_nonneg x)]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => t * ρ (t : ℂ)) (a := 0) (b := 1) ‖x‖
  simp only [mul_zero, mul_one, smul_eq_mul] at hscale
  rw [← hscale]
  have he : (∫ s in (0 : ℝ)..1, (‖x‖ * s) * ρ ((‖x‖ * s : ℝ) : ℂ)) =
      ‖x‖ * equilibriumRadialAverage ρ x := by
    rw [equilibriumRadialAverage, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have hrho : ρ ((‖x‖ * s : ℝ) : ℂ) = ρ (s • x) := by
      apply hρrad
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) hs'.1),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hs'.1]
      ring
    change (‖x‖ * s) * ρ ((‖x‖ * s : ℝ) : ℂ) = ‖x‖ * (s * ρ (s • x))
    rw [hrho]
    ring
  rw [he]
  ring

end RepulsiveCoulomb
