import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEnergy

/-! The actual doubly circle-smeared Coulomb interaction. The single cutoff is
not assumed to be positive type. This module proves the precise product-measure
identity, diagonal self-energy and error decomposition that will be used with
zero-mass logarithmic positivity. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
namespace RepulsiveCoulomb

def equilibriumDoubleCircularKernel (ε : ℝ) (x y : ℂ) : ℝ :=
  ∫ z : ℂ, equilibriumCircularKernel ε (z - y) ∂equilibriumCircleMeasure x ε

theorem equilibriumCircularKernel_circle_integrable {ε : ℝ} (hε : 0 < ε)
    (c x : ℂ) (δ : ℝ) :
    Integrable (fun z : ℂ => equilibriumCircularKernel ε (z - x))
      (equilibriumCircleMeasure c δ) := by
  have hc : Continuous (fun z : ℂ => equilibriumCircularKernel ε (z - x)) :=
    (equilibriumCircularKernel_continuous hε).comp (continuous_id.sub continuous_const)
  exact integrable_equilibriumCircleMeasure_of_circleIntegrable c δ hc.measurable
    hc.continuousOn.circleIntegrable'

/-- The kernel is the actual interaction of two singular circular probability
measures. Its Fubini condition is proved in CircleEnergy, not assumed here. -/
theorem equilibriumDoubleCircularKernel_eq_energy {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularKernel ε x y =
      ∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂(equilibriumCircleMeasure x ε).prod (equilibriumCircleMeasure y ε) := by
  rw [integral_prod _ (equilibriumCircle_logEnergy_integrable x y ε hε)]
  unfold equilibriumDoubleCircularKernel
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    have he : (fun w : ℂ => equilibriumLogKernel (z - w)) =
        (fun w : ℂ => equilibriumLogKernel (w - z)) := by
      funext w
      simp only [equilibriumLogKernel, norm_sub_rev]
    change equilibriumCircularKernel ε (z - y) =
      ∫ w : ℂ, equilibriumLogKernel (z - w) ∂equilibriumCircleMeasure y ε
    rw [he, equilibriumCircleMeasure_log_potential y z hε]
    simp only [equilibriumCircularKernel, norm_sub_rev])

theorem equilibriumDoubleCircularKernel_symm {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularKernel ε x y = equilibriumDoubleCircularKernel ε y x := by
  rw [equilibriumDoubleCircularKernel_eq_energy hε,
    equilibriumDoubleCircularKernel_eq_energy hε]
  have hs := integral_prod_swap (μ := equilibriumCircleMeasure x ε)
    (ν := equilibriumCircleMeasure y ε)
    (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
  simpa only [Prod.swap, equilibriumLogKernel, norm_sub_rev] using hs.symm

/-- Exact diagonal self-energy. This determines the log-N constant in the
Onsager bound; double circular smearing introduces no extra self-energy. -/
theorem equilibriumDoubleCircularKernel_self {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    equilibriumDoubleCircularKernel ε x x = -Real.log ε := by
  unfold equilibriumDoubleCircularKernel
  apply integral_eq_const
  have hs : ∀ᵐ z ∂equilibriumCircleMeasure x ε, z ∈ sphere x ε :=
    mem_ae_iff.mpr (equilibriumCircleMeasure_supported x hε.le)
  filter_upwards [hs] with z hz
  have hn : ‖z - x‖ = ε := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz
  simp only [equilibriumCircularKernel, hn, max_self]

/-- The off-origin single-circle error remains actually integrable against
another circle. The isolated exceptional point is removed by nonatomicity. -/
theorem equilibriumCircularError_circle_integrable {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    Integrable (fun z : ℂ => equilibriumCircularError ε (z - y))
      (equilibriumCircleMeasure x ε) := by
  letI := equilibriumCircleMeasure_nullSingleton x hε
  apply ((equilibriumLogKernel_circle_integrable x y ε).sub
    (equilibriumCircularKernel_circle_integrable hε x y ε)).congr
  filter_upwards [(equilibriumCircleMeasure x ε).ae_ne y] with z hz
  exact (equilibriumCircularError_eq_sub hε (sub_ne_zero.mpr hz)).symm

/-- The second circle average adds exactly the averaged first error. -/
theorem equilibriumCircularKernel_sub_double {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumCircularKernel ε (x - y) - equilibriumDoubleCircularKernel ε x y =
      ∫ z : ℂ, equilibriumCircularError ε (z - y) ∂equilibriumCircleMeasure x ε := by
  letI := equilibriumCircleMeasure_nullSingleton x hε
  have he : (fun z : ℂ => equilibriumCircularError ε (z - y)) =ᵐ[equilibriumCircleMeasure x ε]
      (fun z : ℂ => equilibriumLogKernel (z - y) - equilibriumCircularKernel ε (z - y)) := by
    filter_upwards [(equilibriumCircleMeasure x ε).ae_ne y] with z hz
    exact equilibriumCircularError_eq_sub hε (sub_ne_zero.mpr hz)
  rw [integral_congr_ae he, integral_sub (equilibriumLogKernel_circle_integrable x y ε)
    (equilibriumCircularKernel_circle_integrable hε x y ε),
    equilibriumCircleMeasure_log_potential x y hε]
  rfl

theorem equilibriumDoubleCircularKernel_le_single {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularKernel ε x y ≤ equilibriumCircularKernel ε (x - y) := by
  have hp : (0 : ℝ) ≤ ∫ z : ℂ, equilibriumCircularError ε (z - y)
      ∂equilibriumCircleMeasure x ε :=
    integral_nonneg (fun z : ℂ => equilibriumCircularError_nonneg ε (z - y))
  rw [← equilibriumCircularKernel_sub_double hε x y] at hp
  linarith

/-- The singular pointwise comparison is stated only for distinct points. -/
theorem equilibriumDoubleCircularKernel_le_log {ε : ℝ} (hε : 0 < ε)
    {x y : ℂ} (hxy : x ≠ y) :
    equilibriumDoubleCircularKernel ε x y ≤ equilibriumLogKernel (x - y) :=
  (equilibriumDoubleCircularKernel_le_single hε x y).trans
    (equilibriumCircularKernel_le_logKernel hε (sub_ne_zero.mpr hxy))

/-- Exact double-error identity on the true collision-free pair domain. -/
theorem equilibriumLogKernel_sub_double {ε : ℝ} (hε : 0 < ε) {x y : ℂ} (hxy : x ≠ y) :
    equilibriumLogKernel (x - y) - equilibriumDoubleCircularKernel ε x y =
      equilibriumCircularError ε (x - y) +
        ∫ z : ℂ, equilibriumCircularError ε (z - y) ∂equilibriumCircleMeasure x ε := by
  rw [equilibriumCircularError_eq_sub hε (sub_ne_zero.mpr hxy),
    ← equilibriumCircularKernel_sub_double hε x y]
  ring

end RepulsiveCoulomb
