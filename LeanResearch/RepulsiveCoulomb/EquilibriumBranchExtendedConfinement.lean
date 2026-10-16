import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedKernel

/-! Nonnegative shifted confinement and full-P2 negative interaction control.
These hold for arbitrary finite measures, including singular measures. They do
not assume the positive logarithmic energy is finite. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

def equilibriumShiftedConfinement (x : ℂ) : ℝ :=
  ‖x‖ ^ 2 / 4 - equilibriumLogMoment x + 1

theorem equilibriumShiftedConfinement_continuous : Continuous equilibriumShiftedConfinement :=
  ((continuous_norm.pow 2).div_const 4).sub equilibriumLogMoment_continuous |>.add continuous_const

theorem equilibriumShiftedConfinement_nonneg (x : ℂ) :
    0 ≤ equilibriumShiftedConfinement x := by
  have hl := equilibriumLogMoment_le_norm x
  have hs := sq_nonneg (‖x‖ - 2)
  unfold equilibriumShiftedConfinement
  nlinarith

/-- Exact coercive pointwise bound needed on the full probability-measure
space; it does not depend on an already finite entropy or interaction. -/
theorem equilibriumShiftedConfinement_coercive (x : ℂ) :
    ‖x‖ ^ 2 / 8 - 1 ≤ equilibriumShiftedConfinement x := by
  have hl := equilibriumLogMoment_le_norm x
  have hs := sq_nonneg (‖x‖ - 4)
  unfold equilibriumShiftedConfinement
  nlinarith

theorem equilibriumLogMoment_measure_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) : Integrable equilibriumLogMoment μ := by
  apply (hμ2.add (integrable_const ((4 : ℝ)⁻¹))).mono'
    equilibriumLogMoment_continuous.measurable.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumLogMoment_nonneg x)]
    simpa only [one_mul, mul_one] using equilibriumLogMoment_le_quadratic (δ := 1) zero_lt_one x)

theorem equilibriumShiftedConfinement_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) : Integrable equilibriumShiftedConfinement μ :=
  ((hμ2.div_const 4).sub (equilibriumLogMoment_measure_integrable hμ2)).add (integrable_const 1)

/-- The negative logarithmic interaction has finite absolute integral on the
entire P2 domain, even if the positive interaction is infinite. -/
theorem equilibriumLogNegative_product_integrable {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    Integrable (fun p : ℂ × ℂ => max (-equilibriumLogKernel (p.1 - p.2)) 0) (μ.prod μ) := by
  have hL := equilibriumLogMoment_measure_integrable hμ2
  have hmajor := (hL.comp_fst μ).add (hL.comp_snd μ)
  apply hmajor.mono' (((equilibriumLogKernel_measurable.comp
    (measurable_fst.sub measurable_snd)).neg.max measurable_const).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    dsimp only [Pi.add_apply, Function.comp_apply, Pi.neg_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [equilibriumLogKernel_sub_lower p.1 p.2]
    · linarith [equilibriumLogMoment_nonneg p.1, equilibriumLogMoment_nonneg p.2])

end RepulsiveCoulomb
