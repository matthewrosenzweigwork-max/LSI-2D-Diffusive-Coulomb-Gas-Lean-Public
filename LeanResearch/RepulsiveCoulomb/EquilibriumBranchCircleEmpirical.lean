import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDoubleCircular
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The actual normalized circularly smeared empirical probability measure.
Its support is a finite union of planar-null circles, and its self and cross
logarithmic energies are proved integrable for every positive particle number
and smearing radius. No planar-density surrogate is used for the circles. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal BigOperators Classical
namespace RepulsiveCoulomb

def equilibriumCircleEmpirical {N : ℕ} (z : Fin N → ℂ) (ε : ℝ) : Measure ℂ :=
  (N : ℝ≥0∞)⁻¹ • Measure.sum (fun i : Fin N => equilibriumCircleMeasure (z i) ε)

def equilibriumCircleEmpiricalSupport {N : ℕ} (z : Fin N → ℂ) (ε : ℝ) : Set ℂ :=
  ⋃ i : Fin N, sphere (z i) ε

theorem equilibriumCircleEmpirical_probability {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (ε : ℝ) : IsProbabilityMeasure (equilibriumCircleEmpirical z ε) := by
  refine ⟨?_⟩
  unfold equilibriumCircleEmpirical
  rw [Measure.smul_apply, Measure.sum_apply_of_countable]
  simp only [measure_univ, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by finiteness)

theorem equilibriumCircleEmpirical_nullSingleton {N : ℕ} (z : Fin N → ℂ)
    {ε : ℝ} (hε : 0 < ε) : NullSingletonClass (equilibriumCircleEmpirical z ε) := by
  refine ⟨fun x => ?_⟩
  unfold equilibriumCircleEmpirical
  rw [Measure.smul_apply, Measure.sum_apply_of_countable]
  simp only [equilibriumCircleMeasure_singleton _ _ hε, tsum_zero, smul_zero]

theorem equilibriumCircleEmpiricalSupport_measurable {N : ℕ} (z : Fin N → ℂ) (ε : ℝ) :
    MeasurableSet (equilibriumCircleEmpiricalSupport z ε) :=
  MeasurableSet.iUnion (fun _ => isClosed_sphere.measurableSet)

theorem equilibriumCircleEmpiricalSupport_volume_zero {N : ℕ} (z : Fin N → ℂ) (ε : ℝ) :
    volume (equilibriumCircleEmpiricalSupport z ε) = 0 :=
  measure_iUnion_null (fun i => equilibriumCircle_support_volume_zero (z i) ε)

theorem equilibriumCircleEmpirical_supported {N : ℕ} (z : Fin N → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    equilibriumCircleEmpirical z ε (equilibriumCircleEmpiricalSupport z ε)ᶜ = 0 := by
  have hi (i : Fin N) : equilibriumCircleMeasure (z i) ε
      (equilibriumCircleEmpiricalSupport z ε)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (subset_iUnion (fun j => sphere (z j) ε) i))
      (equilibriumCircleMeasure_supported (z i) hε)
  unfold equilibriumCircleEmpirical
  rw [Measure.smul_apply, Measure.sum_apply_of_countable]
  simp only [hi, tsum_zero, smul_zero]

theorem equilibriumCircleEmpirical_integrable {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (ε : ℝ) {f : ℂ → ℝ}
    (hf : ∀ i, Integrable f (equilibriumCircleMeasure (z i) ε)) :
    Integrable f (equilibriumCircleEmpirical z ε) := by
  apply (integrable_sum_measure hf Summable.of_finite).smul_measure
  exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')

theorem integral_equilibriumCircleEmpirical {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (ε : ℝ) {f : ℂ → ℝ}
    (hf : ∀ i, Integrable f (equilibriumCircleMeasure (z i) ε)) :
    (∫ x, f x ∂equilibriumCircleEmpirical z ε) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ x, f x ∂equilibriumCircleMeasure (z i) ε := by
  unfold equilibriumCircleEmpirical
  rw [integral_smul_measure, integral_sum_measure (integrable_sum_measure hf Summable.of_finite)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, tsum_fintype]

/-- Actual absolute self-energy integrability, including coincident centers. -/
theorem equilibriumCircleEmpirical_logEnergy_integrable {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleEmpirical z ε).prod (equilibriumCircleEmpirical z ε)) := by
  have hc : (N : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
  unfold equilibriumCircleEmpirical
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_sum]
  exact ((integrable_sum_measure
    (fun p : Fin N × Fin N => equilibriumCircle_logEnergy_integrable (z p.1) (z p.2) ε hε)
    Summable.of_finite).smul_measure hc).smul_measure hc

/-- Actual circle-empirical versus reference cross integrability follows from
the reference first moment, with no density bound or regularity assumption. -/
theorem equilibriumCircleEmpirical_cross_integrable {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμ : Integrable (fun x : ℂ => ‖x‖) μ) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleEmpirical z ε).prod μ) := by
  have hc : (N : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
  have hi (i : Fin N) : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleMeasure (z i) ε).prod μ) := by
    simpa only [Function.comp_def, Prod.swap, equilibriumLogKernel, norm_sub_rev] using
      (equilibriumMeasure_circle_logEnergy_integrable hμ (z i) hε).swap
  unfold equilibriumCircleEmpirical
  rw [Measure.prod_smul_left, Measure.prod_sum_left]
  exact (integrable_sum_measure hi Summable.of_finite).smul_measure hc

end RepulsiveCoulomb
