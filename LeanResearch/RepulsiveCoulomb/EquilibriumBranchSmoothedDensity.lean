module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

/-! The actual circle-smoothed planar reference density. Its measure is proved
equal to circle convolution of the original law by nonnegative Fubini and
translation invariance. The circular empirical measure itself remains singular.
This is the reference required for the doubly regularized energy positivity. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumSmoothedDensity (ε : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ z : ℂ, ρ (x - z) ∂equilibriumCircleMeasure 0 ε

theorem equilibriumSmoothedDensity_measurable (ε : ℝ) {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable (equilibriumSmoothedDensity ε ρ) :=
  ((hρ.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'
    (ν := equilibriumCircleMeasure 0 ε)).measurable

theorem equilibriumSmoothedDensity_nonneg (ε : ℝ) {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (x : ℂ) :
    0 ≤ equilibriumSmoothedDensity ε ρ x := integral_nonneg (fun z => hρ0 (x - z))

theorem equilibriumSmoothedDensity_row_integrable (ε : ℝ) {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (x : ℂ) :
    Integrable (fun z : ℂ => ρ (x - z)) (equilibriumCircleMeasure 0 ε) := by
  apply (integrable_const M).mono' (hρm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    change ‖ρ (x - z)‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 (x - z))]
    exact hρM (x - z))

/-- Circle smoothing preserves the same pointwise density cap, exactly. -/
theorem equilibriumSmoothedDensity_le (ε : ℝ) {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (x : ℂ) :
    equilibriumSmoothedDensity ε ρ x ≤ M := by
  have h := integral_mono (equilibriumSmoothedDensity_row_integrable ε hρm hρ0 hρM x)
    (integrable_const M) (fun z => hρM (x - z))
  simpa only [equilibriumSmoothedDensity, integral_const, probReal_univ, one_smul] using h

/-- The actual withDensity law equals circle convolution, for a measurable
bounded nonnegative density. This is a genuine measure identity, not an assumed
formal exchange of the circle measure with planar volume. -/
theorem equilibriumSmoothedDensity_measure (ε : ℝ) {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) :
    equilibriumDensityMeasure (equilibriumSmoothedDensity ε ρ) =
      (equilibriumCircleMeasure 0 ε).conv (equilibriumDensityMeasure ρ) := by
  letI : SigmaFinite (equilibriumDensityMeasure ρ) := by
    unfold equilibriumDensityMeasure
    infer_instance
  have hs := equilibriumSmoothedDensity_measurable ε hρm
  have he (x : ℂ) : ENNReal.ofReal (equilibriumSmoothedDensity ε ρ x) =
      ∫⁻ z : ℂ, ENNReal.ofReal (ρ (x - z)) ∂equilibriumCircleMeasure 0 ε :=
    ofReal_integral_eq_lintegral_ofReal (equilibriumSmoothedDensity_row_integrable ε hρm hρ0 hρM x)
      (Eventually.of_forall (fun z => hρ0 (x - z)))
  apply Measure.ext_of_lintegral
  intro φ hφ
  calc
    (∫⁻ x, φ x ∂equilibriumDensityMeasure (equilibriumSmoothedDensity ε ρ)) =
        ∫⁻ x : ℂ, ENNReal.ofReal (equilibriumSmoothedDensity ε ρ x) * φ x :=
      lintegral_withDensity_eq_lintegral_mul volume hs.ennreal_ofReal hφ
    _ = ∫⁻ x : ℂ, ∫⁻ z : ℂ, ENNReal.ofReal (ρ (x - z)) * φ x
        ∂equilibriumCircleMeasure 0 ε ∂volume := by
      apply lintegral_congr
      intro x
      rw [he]
      have hx : Measurable (fun z : ℂ => ENNReal.ofReal (ρ (x - z))) :=
        hρm.ennreal_ofReal.comp (measurable_const.sub measurable_id)
      exact (lintegral_mul_const (μ := equilibriumCircleMeasure 0 ε) (φ x) hx).symm
    _ = ∫⁻ z : ℂ, ∫⁻ x : ℂ, ENNReal.ofReal (ρ (x - z)) * φ x
        ∂volume ∂equilibriumCircleMeasure 0 ε := by
      apply lintegral_lintegral_swap
      exact ((hρm.ennreal_ofReal.comp (measurable_fst.sub measurable_snd)).mul
        (hφ.comp measurable_fst)).aemeasurable
    _ = ∫⁻ z : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (ρ y) * φ (z + y)
        ∂volume ∂equilibriumCircleMeasure 0 ε := by
      apply lintegral_congr
      intro z
      have ht := lintegral_add_left_eq_self (μ := (volume : Measure ℂ))
        (fun x : ℂ => ENNReal.ofReal (ρ (x - z)) * φ x) z
      simpa only [add_sub_cancel_left] using ht.symm
    _ = ∫⁻ x, φ x ∂(equilibriumCircleMeasure 0 ε).conv (equilibriumDensityMeasure ρ) := by
      rw [Measure.lintegral_conv hφ]
      apply lintegral_congr
      intro z
      have hz : Measurable (fun y : ℂ => φ (z + y)) :=
        hφ.comp (measurable_const.add measurable_id)
      simpa only [equilibriumDensityMeasure, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul volume hρm.ennreal_ofReal hz).symm

/-- The reference smoothing uses the actual constructed law and preserves its
probability normalization and sharp 1/pi cap. -/
theorem equilibriumReference_smoothed_measure {β : ℝ} (R : EquilibriumConstructedReference β) (ε : ℝ) :
    equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density) =
      (equilibriumCircleMeasure 0 ε).conv (R.measure : Measure ℂ) := by
  rw [equilibriumSmoothedDensity_measure ε R.smooth.continuous.measurable
    (fun x => (R.positive x).le) R.cap, R.density_measure]

theorem equilibriumReference_smoothed_probability {β : ℝ} (R : EquilibriumConstructedReference β) (ε : ℝ) :
    IsProbabilityMeasure (equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density)) := by
  rw [equilibriumReference_smoothed_measure R ε]
  infer_instance

theorem equilibriumReference_smoothed_mass {β : ℝ} (R : EquilibriumConstructedReference β) (ε : ℝ) :
    Integrable (equilibriumSmoothedDensity ε R.density) ∧
      (∫ x : ℂ, equilibriumSmoothedDensity ε R.density x) = 1 := by
  letI := equilibriumReference_smoothed_probability R ε
  have hs := equilibriumSmoothedDensity_measurable ε R.smooth.continuous.measurable
  have h0 := equilibriumSmoothedDensity_nonneg ε (fun x => (R.positive x).le)
  have hmass : (∫⁻ x : ℂ, ENNReal.ofReal (equilibriumSmoothedDensity ε R.density x)) = 1 := by
    have h := measure_univ (μ := equilibriumDensityMeasure (equilibriumSmoothedDensity ε R.density))
    simpa only [equilibriumDensityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using h
  have hi := (lintegral_ofReal_ne_top_iff_integrable hs.aestronglyMeasurable
    (Eventually.of_forall h0)).mp (hmass.trans_ne ENNReal.one_ne_top)
  refine ⟨hi, ?_⟩
  have hn : (0 : ℝ) ≤ ∫ x : ℂ, equilibriumSmoothedDensity ε R.density x := integral_nonneg h0
  have he := congrArg ENNReal.toReal hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0),
    ENNReal.toReal_ofReal hn, ENNReal.toReal_one] at he
  exact he

end RepulsiveCoulomb
