import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCrossInteraction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular

/-! A genuine finite-energy mass-filling competitor on a bounded measurable
set of positive planar volume. This supplies the one-sided zero-set variation
without assuming a bounded/smooth thermal minimizer. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped Classical ENNReal
namespace RepulsiveCoulomb

def equilibriumUniformSetDensity (A : Set ℂ) : ℂ → ℝ :=
  A.indicator (fun _ => ((volume A).toReal)⁻¹)

theorem equilibriumUniformSetDensity_measurable {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable (equilibriumUniformSetDensity A) := measurable_const.indicator hA

theorem equilibriumUniformSetDensity_nonneg (A : Set ℂ) (x : ℂ) :
    0 ≤ equilibriumUniformSetDensity A x := by
  by_cases hx : x ∈ A
  · simp only [equilibriumUniformSetDensity, indicator_of_mem hx]
    exact inv_nonneg.mpr ENNReal.toReal_nonneg
  · simp only [equilibriumUniformSetDensity, indicator_of_notMem hx, le_refl]

theorem equilibriumUniformSetDensity_le (A : Set ℂ) (x : ℂ) :
    equilibriumUniformSetDensity A x ≤ ((volume A).toReal)⁻¹ := by
  by_cases hx : x ∈ A
  · simp only [equilibriumUniformSetDensity, indicator_of_mem hx, le_refl]
  · simp only [equilibriumUniformSetDensity, indicator_of_notMem hx]
    exact inv_nonneg.mpr ENNReal.toReal_nonneg

theorem equilibriumUniformSetDensity_integrable {A : Set ℂ} (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) : Integrable (equilibriumUniformSetDensity A) :=
  (integrableOn_const hAfin).integrable_indicator hA

theorem integral_equilibriumUniformSetDensity {A : Set ℂ} (hA : MeasurableSet A)
    (hA0 : volume A ≠ 0) (hAfin : volume A ≠ ∞) :
    (∫ x : ℂ, equilibriumUniformSetDensity A x) = 1 := by
  have hpos := ENNReal.toReal_pos hA0 hAfin
  rw [equilibriumUniformSetDensity, integral_indicator_const _ hA, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

theorem equilibriumUniformSetDensity_secondMoment_integrable {A : Set ℂ}
    (hA : MeasurableSet A) (hAfin : volume A ≠ ∞) {R : ℝ}
    (hR : 0 ≤ R) (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumUniformSetDensity A x) := by
  apply ((equilibriumUniformSetDensity_integrable hA hAfin).const_mul (R ^ 2)).mono' (by
    exact (continuous_norm.measurable.pow_const 2).mul
      (equilibriumUniformSetDensity_measurable hA) |>.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (equilibriumUniformSetDensity_nonneg A x))]
    by_cases hx : x ∈ A
    · exact mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg x) hR |>.mpr (hAR x hx))
        (equilibriumUniformSetDensity_nonneg A x)
    · simp only [equilibriumUniformSetDensity, indicator_of_notMem hx, mul_zero, le_refl])

theorem equilibriumUniformSetDensity_entropy_integrable {A : Set ℂ}
    (hA : MeasurableSet A) (hAfin : volume A ≠ ∞) :
    Integrable (fun x : ℂ => equilibriumUniformSetDensity A x *
      Real.log (equilibriumUniformSetDensity A x)) := by
  apply ((equilibriumUniformSetDensity_integrable hA hAfin).mul_const
    (Real.log (((volume A).toReal)⁻¹))).congr
  exact Eventually.of_forall (fun x => by
    by_cases hx : x ∈ A
    · simp only [equilibriumUniformSetDensity, indicator_of_mem hx]
    · simp only [equilibriumUniformSetDensity, indicator_of_notMem hx, zero_mul])

/-- Actual absolute self-energy of the filling density; its finite logarithmic
moment is derived from the displayed bounded support, not assumed. -/
theorem equilibriumUniformSetDensity_logEnergy_integrable {A : Set ℂ}
    (hA : MeasurableSet A) (hA0 : volume A ≠ 0) (hAfin : volume A ≠ ∞)
    {R : ℝ} (hR : 0 ≤ R) (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    Integrable (fun p : ℂ × ℂ => equilibriumUniformSetDensity A p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumUniformSetDensity A p.2)) (volume.prod volume) := by
  have hm := equilibriumUniformSetDensity_measurable hA
  have h0 := equilibriumUniformSetDensity_nonneg A
  have hi := equilibriumUniformSetDensity_integrable hA hAfin
  have hL := equilibriumLogMoment_mul_integrable hm h0 hi
    (equilibriumUniformSetDensity_secondMoment_integrable hA hAfin hR hAR)
  exact equilibriumCrossInteraction_integrable hm h0 hi hL hm h0
    (equilibriumUniformSetDensity_le A) hi (integral_equilibriumUniformSetDensity hA hA0 hAfin) hL

theorem equilibriumUniformSetDensity_disjoint {A : Set ℂ} {ρ : ℂ → ℝ}
    (hA : ∀ x ∈ A, ρ x = 0) (x : ℂ) : ρ x * equilibriumUniformSetDensity A x = 0 := by
  by_cases hx : x ∈ A
  · rw [hA x hx, zero_mul]
  · simp only [equilibriumUniformSetDensity, indicator_of_notMem hx, mul_zero]

/-- A positive-volume zero set contains an actual compact positive-volume
piece, so the finite-volume and bounded-support hypotheses of the filler are
discharged rather than postulated in a minimizer-positivity argument. -/
theorem equilibrium_zeroSet_contains_filling_set {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hzero : volume {x : ℂ | ρ x = 0} ≠ 0) :
    ∃ (A : Set ℂ) (R : ℝ), MeasurableSet A ∧ volume A ≠ 0 ∧ volume A ≠ ∞ ∧
      0 < R ∧ (∀ x ∈ A, ‖x‖ ≤ R) ∧ (∀ x ∈ A, ρ x = 0) := by
  have hZ : MeasurableSet {x : ℂ | ρ x = 0} := measurableSet_eq_fun hρm measurable_const
  obtain ⟨A, hAZ, hAc, hAv⟩ := hZ.exists_lt_isCompact (pos_iff_ne_zero.mpr hzero)
  obtain ⟨R, hR, hAR⟩ := hAc.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  refine ⟨A, R, hAc.measurableSet, hAv.ne', hAc.measure_lt_top.ne, hR, ?_, ?_⟩
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hAR hx
  · intro x hx
    exact hAZ hx

end RepulsiveCoulomb
