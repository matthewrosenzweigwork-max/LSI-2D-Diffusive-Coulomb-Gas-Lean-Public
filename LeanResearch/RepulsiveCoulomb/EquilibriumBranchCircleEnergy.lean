import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual logarithmic energies for the singular circular probability measures.
The row estimate proves absolute integrability even when the point lies on the
circle. It supplies all circle--circle energies, including coincident circles,
without identifying a circle measure with a planar density. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Transport actual circle integrability to the normalized angular pushforward. -/
theorem integrable_equilibriumCircleMeasure_of_circleIntegrable (c : ℂ) (ε : ℝ)
    {f : ℂ → ℝ} (hfm : Measurable f) (hf : CircleIntegrable f c ε) :
    Integrable f (equilibriumCircleMeasure c ε) := by
  unfold equilibriumCircleMeasure
  apply (integrable_map_measure hfm.aestronglyMeasurable
    (measurable_circleMap c ε).aemeasurable).mpr
  have hi : IntegrableOn (fun θ : ℝ => f (circleMap c ε θ)) (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hf
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne')

/-- The true singular logarithm is integrable on every circle, including at a
point of the circle. This uses the pinned meromorphic log-integrability result. -/
theorem equilibriumLogKernel_circle_integrable (c x : ℂ) (ε : ℝ) :
    Integrable (fun z : ℂ => equilibriumLogKernel (z - x))
      (equilibriumCircleMeasure c ε) := by
  apply integrable_equilibriumCircleMeasure_of_circleIntegrable c ε
    (f := fun z : ℂ => equilibriumLogKernel (z - x))
    (equilibriumLogKernel_measurable.comp (measurable_id.sub measurable_const))
  change CircleIntegrable (fun z : ℂ => -Real.log ‖z - x‖) c ε
  exact (circleIntegrable_log_norm_sub_const (c := c) (a := x) ε).neg

theorem equilibriumCircleMeasure_norm_integrable (c : ℂ) (ε : ℝ) :
    Integrable (fun z : ℂ => ‖z‖) (equilibriumCircleMeasure c ε) :=
  integrable_equilibriumCircleMeasure_of_circleIntegrable c ε continuous_norm.measurable
    continuous_norm.continuousOn.circleIntegrable'

theorem equilibriumCircleMeasure_norm_le (c : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ z ∂equilibriumCircleMeasure c ε, ‖z‖ ≤ ‖c‖ + ε := by
  have hs : ∀ᵐ z ∂equilibriumCircleMeasure c ε, z ∈ sphere c ε :=
    mem_ae_iff.mpr (equilibriumCircleMeasure_supported c hε)
  filter_upwards [hs] with z hz
  exact norm_le_norm_add_const_of_dist_le (Metric.mem_sphere.mp hz).le

/-- The exact regularized potential of the singular circle measure. -/
theorem equilibriumCircleMeasure_log_potential (c x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℂ, equilibriumLogKernel (z - x) ∂equilibriumCircleMeasure c ε) =
      equilibriumCircularKernel ε (c - x) := by
  rw [integral_equilibriumCircleMeasure c ε
    (f := fun z : ℂ => equilibriumLogKernel (z - x))
    (equilibriumLogKernel_measurable.comp (measurable_id.sub measurable_const))]
  exact (equilibriumCircularKernel_eq_circleAverage hε c x).symm

private theorem equilibriumLogKernel_abs_le_self_add_norm (z x : ℂ) :
    |equilibriumLogKernel (z - x)| ≤ equilibriumLogKernel (z - x) + 2 * (‖z‖ + ‖x‖) := by
  have hl := equilibriumLogKernel_sub_lower z x
  have hz := equilibriumLogMoment_le_norm z
  have hx := equilibriumLogMoment_le_norm x
  have hnz := norm_nonneg z
  have hnx := norm_nonneg x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Quantitative absolute row bound, valid at every point x with no exclusion
of the supporting circle. The bound is sufficient for genuine Fubini below. -/
theorem equilibriumCircleMeasure_abs_log_bound (c x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℂ, |equilibriumLogKernel (z - x)| ∂equilibriumCircleMeasure c ε) ≤
      |Real.log ε| + 2 * (‖c‖ + ε + ‖x‖) := by
  have hk := equilibriumLogKernel_circle_integrable c x ε
  have hb : (∫ z : ℂ, |equilibriumLogKernel (z - x)| ∂equilibriumCircleMeasure c ε) ≤
      ∫ z : ℂ, equilibriumLogKernel (z - x) + 2 * (‖c‖ + ε + ‖x‖)
        ∂equilibriumCircleMeasure c ε := by
    apply integral_mono_ae hk.abs (hk.add (integrable_const _))
    filter_upwards [equilibriumCircleMeasure_norm_le c hε.le] with z hz
    dsimp only [Pi.add_apply]
    have he := equilibriumLogKernel_abs_le_self_add_norm z x
    linarith
  rw [integral_add hk (integrable_const _), equilibriumCircleMeasure_log_potential c x hε] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  have hl := Real.log_le_log hε (le_max_left ε ‖c - x‖)
  have habs := neg_le_abs (Real.log ε)
  unfold equilibriumCircularKernel at hb
  linarith

/-- Finite first moment of any actual finite measure is enough for its cross
absolute logarithmic energy with a circle. No density or AC assumption is used. -/
theorem equilibriumMeasure_circle_logEnergy_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℂ => ‖x‖) μ) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      (μ.prod (equilibriumCircleMeasure c ε)) := by
  have hm : Measurable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) :=
    equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)
  have hi (x : ℂ) : Integrable (fun z : ℂ => equilibriumLogKernel (x - z))
      (equilibriumCircleMeasure c ε) := by
    simpa only [equilibriumLogKernel, norm_sub_rev] using
      equilibriumLogKernel_circle_integrable c x ε
  have hmajor : Integrable (fun x : ℂ => |Real.log ε| + 2 * (‖c‖ + ε + ‖x‖)) μ :=
    (integrable_const _).add (((integrable_const _).add hμ).const_mul 2)
  have hn : Integrable (fun x : ℂ => ∫ z : ℂ, ‖equilibriumLogKernel (x - z)‖
      ∂equilibriumCircleMeasure c ε) μ := by
    apply hmajor.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simpa only [Real.norm_eq_abs, equilibriumLogKernel, norm_sub_rev] using
        equilibriumCircleMeasure_abs_log_bound c x hε)
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Eventually.of_forall hi, hn⟩

/-- Genuine circle--circle absolute log-energy finiteness, including equal
centers and equal radii. The product diagonal is treated by integrability,
not by silently replacing the circular measures with planar densities. -/
theorem equilibriumCircle_logEnergy_integrable (c d : ℂ) (δ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleMeasure c δ).prod (equilibriumCircleMeasure d ε)) :=
  equilibriumMeasure_circle_logEnergy_integrable (equilibriumCircleMeasure_norm_integrable c δ)
    d hε

end RepulsiveCoulomb
