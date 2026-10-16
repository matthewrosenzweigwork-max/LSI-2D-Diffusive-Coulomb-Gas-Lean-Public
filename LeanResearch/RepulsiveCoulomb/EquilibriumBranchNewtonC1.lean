import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonRadiusDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Asymptotics.Lemmas

/-! A global C1 Newton potential for bounded measurable radial densities.
Continuity of cumulative mass and the quadratic origin estimate are proved
before differentiability is used. The origin derivative is zero, and its
continuity follows from the actual ball-mass bound M*pi*r^2. -/
noncomputable section
open MeasureTheory Real Set Filter Metric Asymptotics
open scoped Topology RealInnerProductSpace
namespace RepulsiveCoulomb

def equilibriumNewtonDerivative (μ : Measure ℂ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  (-equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2) • innerSL ℝ x

theorem equilibriumNewtonDerivative_zero (μ : Measure ℂ) : equilibriumNewtonDerivative μ 0 = 0 := by
  simp only [equilibriumNewtonDerivative, norm_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero, zero_smul]

theorem equilibriumNorm_hasFDerivAt {x : ℂ} (hx : x ≠ 0) :
    HasFDerivAt (fun y : ℂ => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have he : (fun y : ℂ => Real.sqrt (‖y‖ ^ 2)) = (fun y : ℂ => ‖y‖) :=
    funext (fun y => Real.sqrt_sq (norm_nonneg y))
  rw [he, Real.sqrt_sq (norm_nonneg x)] at hd
  convert hd using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hn] <;> ring

/-- The ball-mass estimate yields a linear bound for the full derivative norm. -/
theorem equilibriumNewtonDerivative_norm_le {ρ : ℂ → ℝ} {M : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M) (x : ℂ) :
    ‖equilibriumNewtonDerivative (equilibriumDensityMeasure ρ) x‖ ≤ M * Real.pi * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [equilibriumNewtonDerivative_zero, norm_zero, mul_zero, le_refl]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hm := equilibriumCumulativeMass_density_bound hρ0 hρM hn.le
    have hd : equilibriumCumulativeMass (equilibriumDensityMeasure ρ) ‖x‖ / ‖x‖ ^ 2 ≤ M * Real.pi :=
      (div_le_iff₀ (sq_pos_of_pos hn)).mpr hm
    unfold equilibriumNewtonDerivative
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_nonneg (equilibriumCumulativeMass_nonneg _ _), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right hd hn.le

/-- The apparent inverse radius in the derivative does not create an origin
singularity for bounded densities. -/
theorem equilibriumNewtonDerivative_continuous {ρ : ℂ → ℝ} {M : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    [IsFiniteMeasure (equilibriumDensityMeasure ρ)] :
    Continuous (equilibriumNewtonDerivative (equilibriumDensityMeasure ρ)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, equilibriumNewtonDerivative_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun y : ℂ => M * Real.pi * ‖y‖) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun y : ℂ => M * Real.pi * ‖y‖) :=
        continuous_const.mul continuous_norm
      simpa only [norm_zero, mul_zero] using hc.tendsto (0 : ℂ)
    exact squeeze_zero (fun y => norm_nonneg _) (equilibriumNewtonDerivative_norm_le hρ0 hρM) ht
  · have hc := equilibriumCumulativeMass_continuous (equilibriumDensityMeasure_absolutelyContinuous ρ)
    have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    exact (((hc.comp continuous_norm).continuousAt.neg.div (continuous_norm.pow 2).continuousAt hn).smul
      (innerSL ℝ).continuous.continuousAt)

/-- Quadratic origin increments give the genuine zero Fréchet derivative. -/
theorem equilibriumDensityPotential_hasFDerivAt_origin {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) :
    HasFDerivAt (equilibriumDensityPotential ρ) (0 : ℂ →L[ℝ] ℝ) 0 := by
  have hb : (fun x : ℂ => equilibriumDensityPotential ρ x - equilibriumDensityPotential ρ 0)
      =O[𝓝 0] (fun x : ℂ => ‖x‖ ^ 2) := by
    apply IsBigO.of_bound (M * Real.pi / 2)
    exact Eventually.of_forall (fun x => by
      change ‖equilibriumDensityPotential ρ x - equilibriumDensityPotential ρ 0‖ ≤
        (M * Real.pi / 2) * ‖‖x‖ ^ 2‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      have h := (equilibriumDensityPotential_origin_quadratic hρm hρ0 hρM hρi hρmass hρ2 hUrad x).2
      nlinarith)
  have hl := hb.trans_isLittleO (isLittleO_norm_pow_id (E' := ℂ) (by norm_num : 1 < 2))
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  simpa only [zero_add, ContinuousLinearMap.zero_apply, sub_zero] using hl

/-- The actual Newton derivative at every planar point, including zero. -/
theorem equilibriumDensityPotential_hasFDerivAt_newton {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    (x : ℂ) :
    HasFDerivAt (equilibriumDensityPotential ρ) (equilibriumNewtonDerivative (equilibriumDensityMeasure ρ) x) x := by
  by_cases hx : x = 0
  · subst x
    rw [equilibriumNewtonDerivative_zero]
    exact equilibriumDensityPotential_hasFDerivAt_origin hρm hρ0 hρM hρi hρmass hρ2 hUrad
  · let μ := equilibriumDensityMeasure ρ
    letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
    have hμ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ :=
      (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr hρ2
    have hμ1 : Integrable (fun y : ℂ => ‖y‖) μ := by
      apply (hμ2.add (integrable_const (μ := μ) (1 : ℝ))).mono' continuous_norm.measurable.aestronglyMeasurable
      exact Eventually.of_forall (fun y => by
        dsimp only [Pi.add_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
        nlinarith [sq_nonneg (‖y‖ - 1)])
    have hd := (equilibrium_cutoffPotential_hasDerivAt (equilibriumDensityMeasure_absolutelyContinuous ρ)
      hμ1 (norm_pos_iff.mpr hx)).comp_hasFDerivAt x (equilibriumNorm_hasFDerivAt hx)
    have hlin : (-equilibriumCumulativeMass μ ‖x‖ / ‖x‖) • (‖x‖⁻¹ • innerSL ℝ x) =
        equilibriumNewtonDerivative μ x := by
      rw [smul_smul]
      unfold equilibriumNewtonDerivative
      congr 1
      field_simp [norm_ne_zero_iff.mpr hx] <;> ring
    rw [hlin] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    change equilibriumDensityPotential ρ y = ∫ z : ℂ, equilibriumCircularKernel ‖y‖ z ∂μ
    rw [equilibriumDensityPotential_newton_circle hρm hρ0 hρi hρmass hρ2 hUrad hy,
      integral_equilibriumDensityMeasure hρm hρ0]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by ring)

/-- Bounded measurable radial data already give a global C1 potential. -/
theorem equilibriumDensityPotential_contDiff_one {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) :
    ContDiff ℝ 1 (equilibriumDensityPotential ρ) := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨equilibriumNewtonDerivative (equilibriumDensityMeasure ρ),
    equilibriumNewtonDerivative_continuous hρ0 hρM,
    equilibriumDensityPotential_hasFDerivAt_newton hρm hρ0 hρM hρi hρmass hρ2 hUrad⟩

end RepulsiveCoulomb
