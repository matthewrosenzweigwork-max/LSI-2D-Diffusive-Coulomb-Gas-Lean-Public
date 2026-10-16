module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCumulativeMass
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! The Newton radius derivative for merely measurable densities. The moving
maximum in the cutoff is handled with a uniform local Lipschitz bound and a
derivative at the fixed radius outside its null sphere. No false claim of
pointwise differentiability at every nearby cutoff radius is used. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem equilibriumCircularKernel_measure_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ1 : Integrable (fun y : ℂ => ‖y‖) μ) {r : ℝ} (hr : 0 < r) :
    Integrable (equilibriumCircularKernel r) μ := by
  have h := equilibriumMeasure_circle_logEnergy_integrable hμ1 (0 : ℂ) hr
  apply h.integral_prod_left.congr
  exact Eventually.of_forall (fun y => by
    change (∫ z : ℂ, equilibriumLogKernel (y - z) ∂equilibriumCircleMeasure 0 r) =
      equilibriumCircularKernel r y
    have he : (fun z : ℂ => equilibriumLogKernel (y - z)) =
        (fun z : ℂ => equilibriumLogKernel (z - y)) := by
      funext z
      simp only [equilibriumLogKernel, norm_sub_rev]
    rw [he, equilibriumCircleMeasure_log_potential 0 y hr]
    simp only [equilibriumCircularKernel, zero_sub, norm_neg])

/-- Uniform local Lipschitz control in the cutoff radius, independent of y. -/
theorem equilibriumCircularKernel_radius_lipschitz {a : ℝ} (ha : 0 < a) (y : ℂ) :
    LipschitzOnWith (Real.nnabs a⁻¹) (fun r : ℝ => equilibriumCircularKernel r y) (Ioi a) := by
  have hl : LipschitzOnWith (Real.nnabs a⁻¹) (fun u : ℝ => -Real.log u) (Ioi a) := by
    apply (convex_Ioi a).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun u : ℝ => -u⁻¹)
    · intro u hu
      exact (Real.hasDerivAt_log (ha.trans hu).ne').neg.hasDerivWithinAt
    · intro u hu
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_pos (inv_pos.mpr (ha.trans hu)), Real.coe_nnabs, abs_of_pos (inv_pos.mpr ha)]
      exact (inv_le_inv₀ (ha.trans hu) ha).mpr hu.le
  have hm : LipschitzOnWith 1 (fun r : ℝ => max r ‖y‖) (Ioi a) :=
    (LipschitzWith.id.max_const ‖y‖).lipschitzOnWith
  have hp : MapsTo (fun r : ℝ => max r ‖y‖) (Ioi a) (Ioi a) :=
    fun r hr => by
      change a < max r ‖y‖
      exact (show a < r from hr).trans_le (le_max_left _ _)
  simpa only [mul_one, Function.comp_def, equilibriumCircularKernel] using hl.comp hm hp

/-- The cutoff has its expected derivative at a fixed radius off the sphere. -/
theorem equilibriumCircularKernel_hasDerivAt_radius {r : ℝ} (hr : 0 < r) (y : ℂ)
    (hy : ‖y‖ ≠ r) :
    HasDerivAt (fun t : ℝ => equilibriumCircularKernel t y)
      ((ball (0 : ℂ) r).indicator (fun _ => -r⁻¹) y) r := by
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have hym : y ∈ ball (0 : ℂ) r := by simpa only [Metric.mem_ball, dist_zero_right] using hlt
    rw [Set.indicator_of_mem hym]
    apply (Real.hasDerivAt_log hr.ne').neg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hlt] with t ht
    change ‖y‖ < t at ht
    simp only [equilibriumCircularKernel, max_eq_left ht.le, Pi.neg_apply]
  · have hym : y ∉ ball (0 : ℂ) r := by
      simp only [Metric.mem_ball, dist_zero_right, not_lt]
      exact hgt.le
    rw [Set.indicator_of_notMem hym]
    apply (hasDerivAt_const r (-Real.log ‖y‖)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hgt] with t ht
    change t < ‖y‖ at ht
    simp only [equilibriumCircularKernel, max_eq_right ht.le]

/-- Genuine differentiation of the cutoff potential under the actual finite
reference. Absolute continuity excludes its one fixed exceptional sphere. -/
theorem equilibrium_cutoffPotential_hasDerivAt {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hAC : μ ≪ volume) (hμ1 : Integrable (fun y : ℂ => ‖y‖) μ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => ∫ y : ℂ, equilibriumCircularKernel t y ∂μ)
      (-equilibriumCumulativeMass μ r / r) r := by
  let D : ℂ → ℝ := (ball (0 : ℂ) r).indicator (fun _ => -r⁻¹)
  have hFmeas (t : ℝ) : AEStronglyMeasurable (fun y : ℂ => equilibriumCircularKernel t y) μ := by
    exact ((Real.measurable_log.comp (measurable_const.max continuous_norm.measurable)).neg).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable D μ := (measurable_const.indicator measurableSet_ball).aestronglyMeasurable
  have hs : μ (sphere (0 : ℂ) r) = 0 := hAC (equilibriumCircle_support_volume_zero 0 r)
  have hderiv : ∀ᵐ y ∂μ, HasDerivAt (fun t : ℝ => equilibriumCircularKernel t y) (D y) r := by
    filter_upwards [compl_mem_ae_iff.mpr hs] with y hy
    apply equilibriumCircularKernel_hasDerivAt_radius hr
    simpa only [Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hy
  have hd := (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := μ) (F := fun t y => equilibriumCircularKernel t y) (F' := D)
    (s := Ioi (r / 2)) (bound := fun _ => (r / 2)⁻¹)
    (Ioi_mem_nhds (by linarith : r / 2 < r)) (Eventually.of_forall hFmeas)
    (equilibriumCircularKernel_measure_integrable hμ1 hr) hDmeas
    (Eventually.of_forall (equilibriumCircularKernel_radius_lipschitz (half_pos hr)))
    (integrable_const _) hderiv).2
  have he : (∫ y : ℂ, D y ∂μ) = -equilibriumCumulativeMass μ r / r := by
    rw [show D = (ball (0 : ℂ) r).indicator (fun _ => -r⁻¹) from rfl,
      integral_indicator_const (-r⁻¹) measurableSet_ball]
    simp only [smul_eq_mul, equilibriumCumulativeMass, div_eq_mul_inv]
    ring
  rwa [he] at hd

end RepulsiveCoulomb
