import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSmoothedRepulsivity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleTranslation

/-! Exact transport of both cross and reference self terms through the actual
circle-smoothed reference. The same double circular kernel appears in all
terms; the unsmeared-reference Onsager estimate is not used for this identity. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

/-- An integrable test against the actual smoothed law is the actual mixture
of its integrals against the translated circles. Fubini is justified by the
pushforward integrability condition, not a formal signed-integral swap. -/
theorem integral_equilibriumReference_smoothed {β : ℝ}
    (R : EquilibriumConstructedReference β) (ε : ℝ) {f : ℂ → ℝ} (hfm : Measurable f)
    (hfi : Integrable f (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) :
    (∫ x : ℂ, f x ∂equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) =
      ∫ y : ℂ, ∫ z : ℂ, f z ∂equilibriumCircleMeasure y ε ∂R.measure := by
  rw [equilibriumReference_smoothed_measure R ε] at hfi ⊢
  have hF : Integrable (fun p : ℂ × ℂ => f (p.1 + p.2))
      ((equilibriumCircleMeasure 0 ε).prod R.measure) :=
    (integrable_map_measure hfm.aestronglyMeasurable
      (measurable_fst.add measurable_snd).aemeasurable).mp hfi
  rw [integral_conv hfi, integral_integral_swap hF]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => integral_equilibriumCircleMeasure_translate ε y hfm)

/-- The single cutoff has an actual integrable row against every finite measure
with first moment. This follows from the genuine circle/background log energy. -/
theorem equilibriumCircularKernel_shift_measure_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun y : ℂ => ‖y‖) μ) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumCircularKernel ε (x - y)) μ := by
  have hi := (equilibriumMeasure_circle_logEnergy_integrable hμ x hε).integral_prod_left
  apply hi.congr
  exact Eventually.of_forall (fun y => by
    change (∫ z : ℂ, equilibriumLogKernel (y - z) ∂equilibriumCircleMeasure x ε) =
      equilibriumCircularKernel ε (x - y)
    have he : (fun z : ℂ => equilibriumLogKernel (y - z)) =
        (fun z : ℂ => equilibriumLogKernel (z - y)) := by
      funext z
      simp only [equilibriumLogKernel, norm_sub_rev]
    rw [he, equilibriumCircleMeasure_log_potential x y hε])

/-- Smearing the reference in the cutoff cross potential produces exactly the
double kernel, including all spatial diagonal values. -/
theorem equilibriumReference_smoothed_cutoff_integral {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularKernel ε (x - y)
      ∂equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) =
      ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure := by
  letI := equilibriumReference_smoothed_probability R ε
  have hμ := equilibriumMeasure_norm_integrable_of_secondMoment
    (equilibriumReference_smoothed_secondMoment_integrable hβ R hε.le)
  rw [integral_equilibriumReference_smoothed R ε
    (f := fun y : ℂ => equilibriumCircularKernel ε (x - y))
    ((equilibriumCircularKernel_continuous hε).measurable.comp (measurable_const.sub measurable_id))
    (equilibriumCircularKernel_shift_measure_integrable hμ hε x)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    have he : (fun z : ℂ => equilibriumCircularKernel ε (x - z)) =
        (fun z : ℂ => equilibriumCircularKernel ε (z - x)) := by
      funext z
      simp only [equilibriumCircularKernel, norm_sub_rev]
    change (∫ z : ℂ, equilibriumCircularKernel ε (x - z) ∂equilibriumCircleMeasure y ε) =
      equilibriumDoubleCircularKernel ε x y
    rw [he]
    exact equilibriumDoubleCircularKernel_symm hε y x)

/-- Exact cross term with the consistently smoothed reference. -/
theorem equilibriumReference_double_smoothed_crossEnergy {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumCircleEmpirical z ε).prod
        (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ y : ℂ, equilibriumDoubleCircularKernel ε (z i) y ∂R.measure := by
  letI := equilibriumReference_smoothed_probability R ε
  rw [equilibriumCircleEmpirical_crossEnergy hN z hε
    (equilibriumMeasure_norm_integrable_of_secondMoment
      (equilibriumReference_smoothed_secondMoment_integrable hβ R hε.le))]
  simp_rw [equilibriumReference_smoothed_cutoff_integral hβ R hε]

/-- Exact reference self term with both reference variables smoothed. The
iterated double-kernel integral is literal; its product integrability is
established separately from the positive error-moment bound. -/
theorem equilibriumReference_double_smoothed_selfEnergy {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)).prod
        (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))) =
      ∫ x : ℂ, ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure ∂R.measure := by
  let μs := equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)
  letI : IsProbabilityMeasure μs := equilibriumReference_smoothed_probability R ε
  have hμnorm : Integrable (fun y : ℂ => ‖y‖) μs :=
    equilibriumMeasure_norm_integrable_of_secondMoment
      (equilibriumReference_smoothed_secondMoment_integrable hβ R hε.le)
  have henergy := equilibriumReference_smoothed_logEnergy_integrable hβ R hε.le
  have hpotm : Measurable (fun x : ℂ => ∫ y : ℂ, equilibriumLogKernel (x - y) ∂μs) :=
    ((equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := μs)).measurable
  rw [integral_prod _ henergy,
    integral_equilibriumReference_smoothed R ε hpotm henergy.integral_prod_left]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    have hcx : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
        ((equilibriumCircleMeasure x ε).prod μs) := by
      simpa only [Function.comp_def, Prod.swap, equilibriumLogKernel, norm_sub_rev] using
        (equilibriumMeasure_circle_logEnergy_integrable hμnorm x hε).swap
    change (∫ z : ℂ, ∫ y : ℂ, equilibriumLogKernel (z - y) ∂μs
      ∂equilibriumCircleMeasure x ε) =
      ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure
    rw [integral_integral_swap (f := fun (z y : ℂ) => equilibriumLogKernel (z - y)) hcx]
    simp_rw [equilibriumCircleMeasure_log_potential x _ hε]
    exact equilibriumReference_smoothed_cutoff_integral hβ R hε x)

end RepulsiveCoulomb
