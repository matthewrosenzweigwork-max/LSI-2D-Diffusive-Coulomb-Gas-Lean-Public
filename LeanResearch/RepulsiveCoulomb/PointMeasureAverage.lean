import LeanResearch.RepulsiveCoulomb.PointBallAverage
import LeanResearch.RepulsiveCoulomb.PointBallMassComparison
import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Identify abstract measure averages with the literal point-weighted integrals.
Open and closed balls have the same restricted measure, not merely the same mass. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem rawPointMeasure_setIntegral {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℂ → ℝ) {S : Set ℂ} (hS : MeasurableSet S) :
    (∫ z in S, f z ∂rawPointMeasure a y) = ∫ z in S, f z * rawPointWeight a y z := by
  unfold rawPointMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (rawPointWeight_continuous ha y).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hS]
  simp only [ENNReal.toReal_ofReal (rawPointWeight_nonneg a y _), smul_eq_mul, mul_comm]

theorem rawPointMeasure_restrict_closedBall_eq_ball {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    (rawPointMeasure a y).restrict (closedBall c r) = (rawPointMeasure a y).restrict (ball c r) := by
  apply Measure.restrict_congr_set
  have hn : ∀ᵐ z ∂rawPointMeasure a y, z ∉ sphere c r := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using rawPointMeasure_sphere a y c r
  filter_upwards [hn] with z hz
  simp only [mem_closedBall, mem_ball, mem_sphere] at *
  exact propext ⟨fun h => lt_of_le_of_ne h hz, le_of_lt⟩

theorem rawPointMeasure_continuous_ball_integrable {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {f : ℂ → ℝ} (hf : Continuous f)
    (c : ℂ) (r : ℝ) : IntegrableOn f (ball c r) (rawPointMeasure a y) := by
  letI := rawPointMeasure_locallyFinite ha y
  have h : IntegrableOn f (closedBall c r) (rawPointMeasure a y) :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)
  exact h.mono_set ball_subset_closedBall

theorem rawPointMeasure_average_eq_literal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    (⨍ z in ball c r, f z ∂rawPointMeasure a y) = rawPointBallAverage a y f c r := by
  rw [← rawPointMeasure_restrict_closedBall_eq_ball a y c r]
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  rw [rawPointMeasure_setIntegral ha y f measurableSet_closedBall,
    rawPointMeasure_closedBall ha y c r,
    ENNReal.toReal_ofReal (integral_nonneg (rawPointWeight_nonneg a y))]
  simp only [rawPointBallAverage, div_eq_mul_inv, mul_comm]

theorem rawPointMeasure_average_tendsto {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) :
    Tendsto (fun r : ℝ => ⨍ z in ball c r, f z ∂rawPointMeasure a y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f c)) := by
  simp_rw [rawPointMeasure_average_eq_literal ha y f c]
  exact rawPointBallAverage_tendsto ha y f hf c

end RepulsiveCoulomb
