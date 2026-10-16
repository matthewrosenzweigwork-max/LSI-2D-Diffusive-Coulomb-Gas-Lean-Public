module

public import LeanResearch.RepulsiveCoulomb.PointStrongSobolevRoot
public import LeanResearch.RepulsiveCoulomb.PowerMeanComparison

@[expose] public section

/-! Actual quadratic local Poincare as a consequence of the checked strong
Sobolev upgrade, with the same explicit analytic input and physical gradient. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_strong_local_poincare {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^ 2 ∂rawPointMeasure a y) ≤
      pointLocalSobolevConstant Q P * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  let μ := (rawPointMeasure a y).restrict (ball c R)
  let u : ℂ → ℝ := fun x => f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using rawPointMeasure_ball_lt_top ha y c R⟩
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (rawPointMeasure_ball_pos ha y c hR).ne' (by simpa [μ] using he)⟩
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 1 ≤ pointSobolevKappa Q := (pointSobolevKappa_gt_one hQ0).le
  have hu : Continuous u := hf.continuous.sub continuous_const
  have hs : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    rawPointMeasure_continuous_ball_integrable ha y (hu.norm.pow 2) c R
  have hp : Integrable (fun x => ‖u x‖ ^ (2 * pointSobolevKappa Q)) μ :=
    rawPointMeasure_continuous_ball_integrable ha y
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * pointSobolevKappa Q)).comp hu.norm) c R
  exact (average_sq_le_average_rpow μ u hκ hs hp).trans
    (rawPointMeasure_strong_sobolev_squared_norm ha hQ hP y hPI f hf c hR)

end RepulsiveCoulomb
