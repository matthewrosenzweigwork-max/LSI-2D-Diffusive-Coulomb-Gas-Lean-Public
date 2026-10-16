import LeanResearch.RepulsiveCoulomb.PointMetricBallGauge
import LeanResearch.RepulsiveCoulomb.RawPointVolumeGrowth

/-! Direct uniform comparison of squared conformal distance with the raw weighted
mass of the Euclidean ball centered at one endpoint. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace RepulsiveCoulomb

def pointMetricVolumeConstant (Q : ℝ) : ℝ := 4 * (2 : ℝ) ^ Q / pointLowerConstant 1 Q

theorem pointMetricVolumeConstant_pos (Q : ℝ) : 0 < pointMetricVolumeConstant Q := by
  exact div_pos (by positivity) (pointLowerConstant_pos 1 Q)

theorem rawPointBallFactor_le_ballIntegral {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * rawPointBallFactor a y c r ≤ pointMetricVolumeConstant Q *
      ∫ w in closedBall c r, rawPointWeight a y w := by
  have hf := rawPointBallFactor_dilate ha hQ y c (r := r / 2) (s := 2)
    (by positivity) (by norm_num)
  have hl := rawPointWeight_ball_integral_lower ha hQ y c (r := r / 2) (by positivity)
  rw [show 2 * (r / 2) = r by ring] at hf hl
  calc
    _ ≤ r ^ 2 * (2 ^ Q * rawPointBallFactor a y c (r / 2)) :=
      mul_le_mul_of_nonneg_left hf (sq_nonneg r)
    _ = pointMetricVolumeConstant Q *
        (pointLowerConstant 1 Q * (r / 2) ^ 2 * rawPointBallFactor a y c (r / 2)) := by
      unfold pointMetricVolumeConstant
      field_simp [ne_of_gt (pointLowerConstant_pos 1 Q)]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (pointMetricVolumeConstant_pos Q).le

theorem pointBallGauge_sq {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c z : ℂ) :
    pointBallGauge a y c z ^ 2 = ‖z - c‖ ^ 2 * rawPointBallFactor a y c ‖z - c‖ := by
  rw [pointBallGauge, mul_pow, Real.sq_sqrt (rawPointBallFactor_nonneg a y c (norm_nonneg _))]

theorem pointConformalEDist_sq_le_ballIntegral {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (c z : ℂ) (hz : z ≠ c) :
    (pointSmoothConformalEDist a y c z).toReal ^ 2 ≤ pointMetricVolumeConstant Q *
      ∫ w in closedBall c ‖z - c‖, rawPointWeight a y w := by
  calc
    _ ≤ pointBallGauge a y c z ^ 2 := by
      have h := pointConformalEDist_le_ballGauge ha y c z
      have hD := ENNReal.toReal_nonneg (a := pointSmoothConformalEDist a y c z)
      nlinarith [pointBallGauge_nonneg a y c z]
    _ = _ := pointBallGauge_sq a y c z
    _ ≤ _ := rawPointBallFactor_le_ballIntegral ha hQ y c (norm_pos_iff.mpr (sub_ne_zero.mpr hz))

theorem ballIntegral_le_pointConformalEDist_sq {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (c z : ℂ) :
    (∫ w in closedBall c ‖z - c‖, rawPointWeight a y w) ≤
      Real.pi * Real.exp (4 * Q) * (pointSmoothConformalEDist a y c z).toReal ^ 2 := by
  have h := pointConformalEDist_ballGauge_lower ha hQ y c z
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (2 * Q)).le
  have he : Real.exp (2 * Q) * Real.exp (-2 * Q) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [← mul_assoc, he, one_mul] at hh
  have hs : pointBallGauge a y c z ^ 2 ≤
      Real.exp (4 * Q) * (pointSmoothConformalEDist a y c z).toReal ^ 2 := by
    have he2 : Real.exp (2 * Q) ^ 2 = Real.exp (4 * Q) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hsq : pointBallGauge a y c z ^ 2 ≤
        (Real.exp (2 * Q) * (pointSmoothConformalEDist a y c z).toReal) ^ 2 := by
      have hB := pointBallGauge_nonneg a y c z
      nlinarith
    simpa only [mul_pow, he2] using hsq
  calc
    _ ≤ Real.pi * (‖z - c‖ ^ 2 * rawPointBallFactor a y c ‖z - c‖) := by
      simpa only [mul_assoc] using rawPointWeight_ball_integral_upper ha y c (norm_nonneg (z - c))
    _ = Real.pi * pointBallGauge a y c z ^ 2 := by rw [pointBallGauge_sq]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs Real.pi_pos.le

end RepulsiveCoulomb
