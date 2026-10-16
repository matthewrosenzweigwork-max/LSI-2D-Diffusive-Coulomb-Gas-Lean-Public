module

public import LeanResearch.RepulsiveCoulomb.PointSquaredWeightRadius
public import LeanResearch.RepulsiveCoulomb.PointDyadicAveragingFubini
public import LeanResearch.RepulsiveCoulomb.WeightedSetMeanCentering

@[expose] public section

/-! The pointwise portion of Bjorn's transfer, explicitly conditional on an
actual double-average gradient estimate. That estimate remains an OPEN input;
this module does not claim a Poincare inequality for the point weights. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointDoubleAverageOscillation {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ⨍ x in ball c r, ⨍ z in ball c r, ‖f x - f z‖ ∂rawPointMeasure a y ∂rawPointMeasure a y

theorem rawPointDoubleAverageOscillation_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : 0 ≤ rawPointDoubleAverageOscillation a y f c r :=
  average_nonneg (fun x => average_nonneg (fun z => norm_nonneg _))

theorem rawPoint_pointwise_transfer_of_double_average_bound {m : ℕ} {Q K : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hK : 0 ≤ K) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f)
    (hO : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        K * r * ⨍ z in ball c (2 * r), g z ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure (fun j => 2 * a j) y)‖ ≤
      ENNReal.ofReal (K * rawPointDoublingConstant (2 * Q)) *
        (∑' n : ℕ, ENNReal.ofReal (dyadicBallRadius (2 * R) n *
          ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y)) +
      ENNReal.ofReal (2 * R * K * rawPointInitialMeanConstant (2 * Q)) *
        ENNReal.ofReal (⨍ z in ball x (4 * R), g z ∂rawPointMeasure a y) := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hQ2 : ∑ j, 2 * a j ≤ 2 * Q := by rw [← Finset.mul_sum]; linarith
  have hbase := rawPointMeasure_global_dyadic_oscillation ha2 hQ2 y f hf c hR hx
  apply hbase.trans
  apply add_le_add
  · calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant (2 * Q) *
          (K * dyadicBallRadius (2 * R) n *
            ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (hO x _ (dyadicBallRadius_pos (by positivity) n)) (rawPointDoublingConstant_pos (2 * Q)).le)
      _ = _ := by
        have he (n : ℕ) : rawPointDoublingConstant (2 * Q) *
            (K * dyadicBallRadius (2 * R) n *
              ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) =
            (K * rawPointDoublingConstant (2 * Q)) * (dyadicBallRadius (2 * R) n *
              ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) := by ring
        simp_rw [he, ENNReal.ofReal_mul (mul_nonneg hK (rawPointDoublingConstant_pos (2 * Q)).le)]
        exact ENNReal.tsum_mul_left
  · have h := mul_le_mul_of_nonneg_left (hO x (2 * R) (by positivity))
      (rawPointInitialMeanConstant_pos (2 * Q)).le
    apply (ENNReal.ofReal_le_ofReal h).trans_eq
    rw [show 2 * (2 * R) = 4 * R by ring]
    have he : rawPointInitialMeanConstant (2 * Q) *
        (K * (2 * R) * ⨍ z in ball x (4 * R), g z ∂rawPointMeasure a y) =
        (2 * R * K * rawPointInitialMeanConstant (2 * Q)) *
          (⨍ z in ball x (4 * R), g z ∂rawPointMeasure a y) := by ring
    rw [he, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by positivity) hK)
      (rawPointInitialMeanConstant_pos (2 * Q)).le)]

end RepulsiveCoulomb
