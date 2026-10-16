module

public import LeanResearch.RepulsiveCoulomb.PointStrongSobolev

@[expose] public section

/-! Literal weighted-average normalization for the strong moment inequality. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_energy_ratio_le_outer_average {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (g : ℂ → ℝ) (hgn : ∀ x, 0 ≤ g x) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball c (11 * R), g x ∂rawPointMeasure a y) / (rawPointMeasure a y).real (ball c R) ≤
      (rawPointGrowthConstant Q * (11 : ℝ) ^ (Q + 2)) *
        (⨍ x in ball c (11 * R), g x ∂rawPointMeasure a y) := by
  have hM : 0 < (rawPointMeasure a y).real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
  have hN : 0 < (rawPointMeasure a y).real (ball c (11 * R)) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c (by positivity)).ne' (rawPointMeasure_ball_lt_top ha y c _).ne
  have hm := rawPointMeasure_growth_real ha hQ y c hR (by norm_num : (1 : ℝ) ≤ 11)
  have hI : 0 ≤ ∫ x in ball c (11 * R), g x ∂rawPointMeasure a y := integral_nonneg hgn
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (∫ x in ball c (11 * R), g x ∂rawPointMeasure a y) /
      (rawPointMeasure a y).real (ball c R) ≤
      (rawPointGrowthConstant Q * (11 : ℝ) ^ (Q + 2)) *
      (((rawPointMeasure a y).real (ball c (11 * R)))⁻¹ * ∫ x in ball c (11 * R), g x ∂rawPointMeasure a y)
  rw [mul_comm _ (∫ x in ball c (11 * R), g x ∂rawPointMeasure a y), ← div_eq_mul_inv, ← mul_div_assoc]
  apply (div_le_div_iff₀ hM hN).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm hI]

theorem rawPointMeasure_strong_sobolev_average_moment {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q) ∂rawPointMeasure a y) ≤
      pointStrongSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
        ((∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) /
          (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q := by
  have h := rawPointMeasure_strong_sobolev_of_poincare ha hQ hP y hPI f hf c hR
  have hM : 0 < (rawPointMeasure a y).real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
  rw [setAverage_eq, smul_eq_mul]
  change ((rawPointMeasure a y).real (ball c R))⁻¹ * _ ≤ _
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hM).mpr
  convert h using 1 <;> ring

end RepulsiveCoulomb
