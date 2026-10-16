import LeanResearch.RepulsiveCoulomb.PointWeakSobolev
import LeanResearch.RepulsiveCoulomb.SobolevCoefficient

/-! Uniform-configuration normalization of the actual weak Sobolev inequality.
The displayed weak Poincare input remains an explicit hypothesis. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointWeakSobolevConstant (Q P : ℝ) : ℝ :=
  rawPointFourfoldConstant Q * (pointHedbergConstant Q P) ^ (2 * pointSobolevKappa Q) *
    (rawPointGrowthConstant Q) ^ (pointSobolevGain Q * (2 * pointSobolevKappa Q))

theorem pointWeakSobolevConstant_pos (Q : ℝ) {P : ℝ} (hP : 0 < P) :
    0 < pointWeakSobolevConstant Q P := by
  unfold pointWeakSobolevConstant
  exact mul_pos (mul_pos (rawPointFourfoldConstant_pos Q)
    (Real.rpow_pos_of_pos (pointHedbergConstant_pos Q hP) _))
    (Real.rpow_pos_of_pos (rawPointGrowthConstant_pos Q) _)

theorem rawPointMeasure_weak_sobolev_normalized {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂rawPointMeasure a y))
    (c : ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ENNReal.ofReal (L ^ (2 * pointSobolevKappa Q)) * rawPointMeasure a y
      {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖} ≤
    ENNReal.ofReal (pointWeakSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
      (rawPointMeasure a y).real (ball c R) *
      ((∫ z in ball c (11 * R), g z ∂rawPointMeasure a y) /
        (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hN : 0 < (rawPointMeasure a y).real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne'
      (rawPointMeasure_ball_lt_top ha y c R).ne
  have hI : 0 ≤ ∫ z in ball c (11 * R), g z ∂rawPointMeasure a y := integral_nonneg hgn
  have hi := ofReal_integral_eq_lintegral_ofReal
    (rawPointMeasure_continuous_ball_integrable ha y hg c (11 * R)) (Eventually.of_forall hgn)
  have h := rawPointMeasure_weak_sobolev_of_poincare ha hQ hP y f g hf hg hgn hPI c hR hL
  rw [← hi, ← ENNReal.ofReal_mul (rawPointFourfoldConstant_pos Q).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by
      apply mul_nonneg (mul_nonneg (pointHedbergConstant_pos Q hP).le hR.le)
      exact Real.rpow_nonneg (pointLocalEnergy_nonneg Q a y c R g hgn) _) _)] at h
  have he := sobolev_distribution_coefficient
    (D := rawPointFourfoldConstant Q) (q := 2 * pointSobolevKappa Q)
    (δ := pointSobolevGain Q) (κ := pointSobolevKappa Q)
    (pointHedbergConstant_pos Q hP).le (rawPointGrowthConstant_pos Q).le hR.le hI hN
    (pointSobolevGain_times_q_add_one hQ0) (lt_trans zero_lt_one (pointSobolevKappa_gt_one hQ0)).ne'
  change _ = pointWeakSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
    (rawPointMeasure a y).real (ball c R) *
    ((∫ z in ball c (11 * R), g z ∂rawPointMeasure a y) / (rawPointMeasure a y).real (ball c R)) ^
      pointSobolevKappa Q at he
  unfold pointLocalEnergy at h
  rwa [he] at h

end RepulsiveCoulomb
