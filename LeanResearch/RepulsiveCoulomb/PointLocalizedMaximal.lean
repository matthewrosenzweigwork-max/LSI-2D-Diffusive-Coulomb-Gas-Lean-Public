module

public import LeanResearch.RepulsiveCoulomb.PointPoincareChain

@[expose] public section

/-! Localization of the maximal operator to the dilated ball used in the
Sobolev argument. The gradient-ball radius is five times the telescoping radius. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem dyadicBallRadius_mul (A R : ℝ) (n : ℕ) :
    dyadicBallRadius (A * R) n = A * dyadicBallRadius R n := by
  unfold dyadicBallRadius
  ring

theorem dyadic_gradient_ball_subset {c x : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ ball c R) (n : ℕ) :
    ball x (5 * dyadicBallRadius (2 * R) n) ⊆ ball c (11 * R) := by
  apply ball_subset_ball'
  have hr := dyadicBallRadius_le (show 0 ≤ 2 * R by positivity) n
  have hd := mem_ball.mp hx
  linarith

theorem rawPointKernelAverage_indicator_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {r : ℝ} (hr : 0 < r)
    (g : ℂ → ℝ≥0∞) (x : ℂ) {S : Set ℂ} (hsub : ball x r ⊆ S) :
    rawPointKernelAverage a y r (S.indicator g) x = rawPointKernelAverage a y r g x := by
  rw [rawPointKernelAverage_eq ha y hr, rawPointKernelAverage_eq ha y hr]
  apply laverage_congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact Set.indicator_of_mem (hsub hz) g

theorem rawPoint_dyadic_average_le_local_maximal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) (g : ℂ → ℝ≥0∞) (n : ℕ) :
    (⨍⁻ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      rawPointDyadicMaximal a y (10 * R) ((ball c (11 * R)).indicator g) x := by
  have hr : 0 < 5 * dyadicBallRadius (2 * R) n := by
    have := dyadicBallRadius_pos (show 0 < 2 * R by positivity) n
    positivity
  rw [← rawPointKernelAverage_eq ha y hr,
    ← rawPointKernelAverage_indicator_eq ha y hr g x (dyadic_gradient_ball_subset hR hx n)]
  have he : 5 * dyadicBallRadius (2 * R) n = dyadicBallRadius (10 * R) n := by
    unfold dyadicBallRadius
    ring
  rw [he]
  exact le_iSup (fun k => rawPointKernelAverage a y (dyadicBallRadius (10 * R) k)
    ((ball c (11 * R)).indicator g) x) n

theorem rawPoint_local_dyadic_maximal_weak_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * rawPointMeasure a y {x | t < rawPointDyadicMaximal a y (10 * R)
      ((ball c (11 * R)).indicator g) x} ≤
      ENNReal.ofReal (rawPointFourfoldConstant Q) * ∫⁻ z in ball c (11 * R), g z ∂rawPointMeasure a y := by
  simpa only [lintegral_indicator measurableSet_ball] using
    rawPointDyadicMaximal_weak_bound ha hQ y (show 0 < 10 * R by positivity)
      ((ball c (11 * R)).indicator g) t

end RepulsiveCoulomb
