module

public import LeanResearch.RepulsiveCoulomb.PointDyadicMeanOscillation
public import LeanResearch.RepulsiveCoulomb.PointDyadicMaximal

@[expose] public section

/-! Pointwise dyadic representation conditional on a displayed weak Poincare
estimate. This is the telescoping step of the Sobolev upgrade, not a proof of
the missing David--Semmes estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_poincare_chain {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂rawPointMeasure a y))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      (∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant Q *
        (P * dyadicBallRadius (2 * R) n *
          Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y)))) +
      ENNReal.ofReal (rawPointInitialMeanConstant Q *
        (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂rawPointMeasure a y))) := by
  apply (rawPointMeasure_global_dyadic_mean_oscillation ha hQ y f hf c hR hx).trans
  apply add_le_add
  · apply ENNReal.tsum_le_tsum
    intro n
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hPI x _ (dyadicBallRadius_pos (by positivity) n)) (rawPointDoublingConstant_pos Q).le)
  · apply ENNReal.ofReal_le_ofReal
    have h := hPI x (2 * R) (by positivity)
    rw [show 5 * (2 * R) = 10 * R by ring] at h
    exact mul_le_mul_of_nonneg_left h (rawPointInitialMeanConstant_pos Q).le

end RepulsiveCoulomb
