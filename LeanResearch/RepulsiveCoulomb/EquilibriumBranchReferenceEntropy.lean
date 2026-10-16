import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedEntropy

/-! Canonical Lebesgue RN density of any absolutely continuous P2 probability
measure and its full extended Gaussian entropy formula. Singular measures are
handled by the actual equivalence of Gaussian and planar volume null sets. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumReferenceDensity (μ : Measure ℂ) (x : ℂ) : ℝ := (μ.rnDeriv volume x).toReal

theorem equilibriumReferenceDensity_measurable (μ : Measure ℂ) :
    Measurable (equilibriumReferenceDensity μ) := (Measure.measurable_rnDeriv μ volume).ennreal_toReal

theorem equilibriumReferenceDensity_nonneg (μ : Measure ℂ) (x : ℂ) :
    0 ≤ equilibriumReferenceDensity μ x := ENNReal.toReal_nonneg

theorem equilibriumReferenceDensity_integrable (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (equilibriumReferenceDensity μ) := Measure.integrable_toReal_rnDeriv

theorem equilibriumReferenceDensity_measure {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) : equilibriumDensityMeasure (equilibriumReferenceDensity μ) = μ := by
  calc
    _ = volume.withDensity (μ.rnDeriv volume) := by
      apply withDensity_congr_ae
      exact (Measure.rnDeriv_lt_top μ volume).mono (fun x hx => ENNReal.ofReal_toReal hx.ne)
    _ = μ := Measure.withDensity_rnDeriv_eq μ volume hμ

theorem integral_equilibriumReferenceDensity {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) : (∫ x : ℂ, equilibriumReferenceDensity μ x) = 1 := by
  simpa only [equilibriumReferenceDensity, probReal_univ] using Measure.integral_toReal_rnDeriv hμ

theorem equilibriumReferenceDensity_secondMoment_integrable {μ : Measure ℂ}
    [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumReferenceDensity μ x) := by
  have h := (integrable_toReal_rnDeriv_mul_iff hμ).mpr hμ2
  simpa only [equilibriumReferenceDensity, mul_comm] using h

theorem integral_equilibriumReferenceDensity_secondMoment {μ : Measure ℂ}
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    (∫ x : ℂ, ‖x‖ ^ 2 * equilibriumReferenceDensity μ x) = (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) := by
  simpa only [equilibriumReferenceDensity, mul_comm] using
    (integral_toReal_rnDeriv_mul hμ (f := fun x : ℂ => ‖x‖ ^ 2))

/-- The entropy correspondence for the actual RN density of every AC P2
probability measure, with no bounded-density or finite-positive-entropy input. -/
theorem equilibriumReferenceEntropy_eq_gaussian_klDiv {a : ℝ} (ha : 0 < a)
    {μ : Measure ℂ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    equilibriumExtendedIntegral volume
      (fun x : ℂ => equilibriumReferenceDensity μ x * Real.log (equilibriumReferenceDensity μ x)) =
      (InformationTheory.klDiv μ (equilibriumGaussianMeasure a) : EReal) -
        (a * (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) - Real.log (a / Real.pi) : ℝ) := by
  have he := equilibriumExtendedEntropy_eq_gaussian_klDiv ha
    (equilibriumReferenceDensity_measurable μ) (equilibriumReferenceDensity_nonneg μ)
    (equilibriumReferenceDensity_integrable μ) (integral_equilibriumReferenceDensity hμ)
    (equilibriumReferenceDensity_secondMoment_integrable hμ hμ2)
  rw [equilibriumReferenceDensity_measure hμ, integral_equilibriumReferenceDensity_secondMoment hμ] at he
  exact he

/-- Gaussian and planar-volume absolute continuity are exactly equivalent. -/
theorem equilibriumGaussian_absolutelyContinuous_iff {a : ℝ} (ha : 0 < a)
    (μ : Measure ℂ) : μ ≪ equilibriumGaussianMeasure a ↔ μ ≪ volume := by
  constructor
  · intro h
    exact h.trans (equilibriumDensityMeasure_absolutelyContinuous (equilibriumGaussian a))
  · intro h
    exact h.trans (volume_absolutelyContinuous_equilibriumGaussianMeasure ha)

theorem equilibriumGaussian_klDiv_eq_top_of_not_ac {a : ℝ} (ha : 0 < a)
    {μ : Measure ℂ} (hμ : ¬ μ ≪ volume) :
    InformationTheory.klDiv μ (equilibriumGaussianMeasure a) = ∞ :=
  InformationTheory.klDiv_of_not_ac (fun h => hμ ((equilibriumGaussian_absolutelyContinuous_iff ha μ).mp h))

end RepulsiveCoulomb
