import LeanResearch.RepulsiveCoulomb.PointWeightedPathArea
import LeanResearch.RepulsiveCoulomb.PlanarFrontierBall

/-! Squared-weight area of an actual bounded region controlled by weighted path
length when its frontier lies in an endpoint-radius ball. No separator asserted. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointSquaredRegionArea_le_rawPointPathLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≤ t) {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hfront : frontier U ⊆ closedBall (γ s) ‖γ t - γ s‖) :
    (rawPointMeasure (fun j => 2 * a j) y).real U ≤
      Real.pi * Real.exp (8 * Q) * rawPointPathLength a y γ s t ^ 2 := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hsub : U ⊆ closedBall (γ s) ‖γ t - γ s‖ :=
    subset_closure.trans (planar_closure_subset_closedBall_of_frontier hU _ _ hfront)
  have hm := ENNReal.toReal_mono
    (rawPointMeasure_closedBall_lt_top ha2 y (γ s) ‖γ t - γ s‖).ne
    (measure_mono hsub : rawPointMeasure (fun j => 2 * a j) y U ≤ _)
  change (rawPointMeasure (fun j => 2 * a j) y).real U ≤
    (rawPointMeasure (fun j => 2 * a j) y).real (closedBall (γ s) ‖γ t - γ s‖) at hm
  unfold Measure.real at hm
  rw [rawPointMeasure_closedBall_eq_ball] at hm
  exact hm.trans (pointSquaredBallArea_le_rawPointPathLength_sq ha hQ y hγ hst)

end RepulsiveCoulomb
