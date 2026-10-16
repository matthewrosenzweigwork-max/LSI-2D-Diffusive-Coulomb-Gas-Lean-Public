import LeanResearch.RepulsiveCoulomb.SmoothDyadicTruncation
import LeanResearch.RepulsiveCoulomb.HalfSupportMean

/-! Smooth truncations are integrable and their actual means are controlled
by a median half-support hypothesis. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem smoothTruncation_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Measurable u)
    {a : ℝ} (ha : 0 < a) : Integrable (fun x => smoothDyadicTruncation a (u x)) μ := by
  have hm : Measurable (fun x => smoothDyadicTruncation a (u x)) :=
    (smoothDyadicTruncation_contDiff a).continuous.measurable.comp hu
  apply (integrable_const a).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothDyadicTruncation_nonneg ha.le _)]
  exact smoothDyadicTruncation_le ha.le _

theorem smoothTruncation_average_le_half_height {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {u : X → ℝ} (hu : Measurable u)
    (hhalf : μ.real {x | 0 < u x} ≤ μ.real univ / 2)
    {a : ℝ} (ha : 0 < a) : (⨍ x, smoothDyadicTruncation a (u x) ∂μ) ≤ a / 2 := by
  apply average_le_half_height_of_half_support μ (measurableSet_lt measurable_const hu) hhalf
    (smoothTruncation_integrable μ hu ha) ha.le (fun x => smoothDyadicTruncation_le ha.le _) ?_
  intro x hx
  exact smoothDyadicTruncation_zero ha ((not_lt.mp hx).trans ha.le)

theorem smoothTruncation_plateau_subset_centered_level {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {u : X → ℝ} (hu : Measurable u)
    (hhalf : μ.real {x | 0 < u x} ≤ μ.real univ / 2)
    {a : ℝ} (ha : 0 < a) :
    {x | 2 * a ≤ u x} ⊆ {x | a / 4 < ‖smoothDyadicTruncation a (u x) -
      (⨍ z, smoothDyadicTruncation a (u z) ∂μ)‖} := by
  intro x hx
  exact half_height_lt_centered_on_plateau μ ha
    (smoothTruncation_average_le_half_height μ hu hhalf ha) (smoothDyadicTruncation_eq_height ha hx)

end RepulsiveCoulomb
