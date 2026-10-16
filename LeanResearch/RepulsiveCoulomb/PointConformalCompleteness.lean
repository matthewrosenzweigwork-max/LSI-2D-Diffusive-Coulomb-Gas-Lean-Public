import LeanResearch.RepulsiveCoulomb.PointConformalRadialBarrier
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Properness and completeness of the finite-puncture smooth conformal metric.
The Euclidean topology identification is used explicitly. No uniform-in-configuration
properness bound is needed or claimed. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointConformal_closedBall_compact {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) (r : ℝ) :
    IsCompact {z : ℂ | (pointSmoothConformalEDist a y z x).toReal ≤ r} := by
  have hclosed : @IsClosed ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      {z : ℂ | (pointSmoothConformalEDist a y z x).toReal ≤ r} := by
    exact @isClosed_closedBall ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace x r
  rw [pointSmoothConformalMetricSpace_topology ha y] at hclosed
  obtain ⟨C, hC, hb⟩ := pointConformal_radial_bound ha y
  apply (isCompact_closedBall (0 : ℂ) (2 * pointConformalRadius y + ‖x‖ + C * |r|)).of_isClosed_subset hclosed
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  have h := hb x z
  rw [pointSmoothConformalEDist_comm a y x z] at h
  have hm := mul_le_mul_of_nonneg_left (hz.trans (le_abs_self r)) hC.le
  linarith

theorem pointSmoothConformalMetricSpace_proper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    @ProperSpace ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace := by
  refine @ProperSpace.mk ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace ?_
  intro x r
  change @IsCompact ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    {z : ℂ | (pointSmoothConformalEDist a y z x).toReal ≤ r}
  rw [pointSmoothConformalMetricSpace_topology ha y]
  exact pointConformal_closedBall_compact ha y x r

theorem pointSmoothConformalMetricSpace_complete {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    @CompleteSpace ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace := by
  let : PseudoMetricSpace ℂ := (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
  let : ProperSpace ℂ := pointSmoothConformalMetricSpace_proper ha y
  exact inferInstanceAs (@CompleteSpace ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace)

end RepulsiveCoulomb
