import LeanResearch.RepulsiveCoulomb.PointWeakSobolevMeasureForm
import LeanResearch.RepulsiveCoulomb.SmoothStrongMean

/-! Complete actual mean-centered strong Sobolev upgrade on the raw weighted
ball, conditional on uniform weak Poincare for all C1 observables. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_strong_sobolev_measure_form {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in ball c R, ENNReal.ofReal
      (‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^ (2 * pointSobolevKappa Q)) ∂rawPointMeasure a y) ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      ENNReal.ofReal (pointWeakSobolevBallFactor Q P a y c R) *
        (ENNReal.ofReal (universalSmoothTruncationConstant ^ 2) *
          ∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂rawPointMeasure a y) ^ pointSobolevKappa Q := by
  let μ := (rawPointMeasure a y).restrict (ball c R)
  let ν := (rawPointMeasure a y).restrict (ball c (11 * R))
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using rawPointMeasure_ball_lt_top ha y c R⟩
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (rawPointMeasure_ball_pos ha y c hR).ne' (by simpa [μ] using he)⟩
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 1 ≤ pointSobolevKappa Q := (pointSobolevKappa_gt_one hQ0).le
  have hq : 1 ≤ 2 * pointSobolevKappa Q := by linarith
  have hfi : Integrable f μ := rawPointMeasure_continuous_ball_integrable ha y hf.continuous c R
  have hb : ∃ L U : ℝ, ∀ᵐ x ∂μ, L ≤ f x ∧ f x ≤ U := by
    obtain ⟨L, hL⟩ := (isCompact_closedBall c R).bddBelow_image hf.continuous.continuousOn
    obtain ⟨U, hU⟩ := (isCompact_closedBall c R).bddAbove_image hf.continuous.continuousOn
    refine ⟨L, U, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ⟨hL (mem_image_of_mem f (ball_subset_closedBall hx)),
      hU (mem_image_of_mem f (ball_subset_closedBall hx))⟩
  have hp (b : ℝ) : Integrable (fun x => ‖f x - b‖ ^ (2 * pointSobolevKappa Q)) μ :=
    rawPointMeasure_continuous_ball_integrable ha y
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * pointSobolevKappa Q)).comp
        (hf.continuous.sub continuous_const).norm) c R
  apply smooth_weak_to_strong_mean μ ν hf hfi hb hq hκ universalSmoothTruncationConstant_pos.le
    universalSmoothTruncationConstant_bound hp
  intro v hv t ht
  exact rawPointMeasure_weak_sobolev_measure_form ha hQ hP y v hv (hPI v hv) c hR ht

end RepulsiveCoulomb
