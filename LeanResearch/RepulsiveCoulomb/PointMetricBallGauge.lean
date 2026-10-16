module

public import LeanResearch.RepulsiveCoulomb.PointRadialMetricLower

@[expose] public section

/-! A direct two-sided, configuration-uniform comparison between the actual
conformal path distance and the explicit radial ball factor. This analytic
comparison does not assert the sharper Bonk--Lang bi-Lipschitz constant. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def pointBallGauge {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c z : ℂ) : ℝ :=
  ‖z - c‖ * Real.sqrt (rawPointBallFactor a y c ‖z - c‖)

theorem rawPointBallFactor_sqrt {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (rawPointBallFactor a y c r) = ∏ j, (r + ‖y j - c‖) ^ (a j / 2) := by
  unfold rawPointBallFactor
  rw [Real.sqrt_prod Finset.univ (fun j _ => Real.rpow_nonneg (by positivity) _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), norm_sub_rev c (y j)]
  congr 1
  ring

theorem pointBallGauge_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c z : ℂ) :
    0 ≤ pointBallGauge a y c z := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem pointConformalEDist_le_ballGauge {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c z : ℂ) :
    (pointSmoothConformalEDist a y c z).toReal ≤ pointBallGauge a y c z := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    (pointSmoothConformalEDist_segment_upper ha y c z)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (norm_nonneg _), pointBallGauge, mul_comm] using h

theorem pointConformalEDist_ballGauge_lower {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (c z : ℂ) :
    Real.exp (-2 * Q) * pointBallGauge a y c z ≤ (pointSmoothConformalEDist a y c z).toReal := by
  by_cases hz : z = c
  · subst z
    simp [pointBallGauge, pointSmoothConformalEDist_self]
  · have h := pointConformalEDist_uniform_radial_lower ha y c z hz
    have hg : pointBallGauge a y c z =
        ‖z - c‖ * ∏ j, (‖z - c‖ + ‖y j - c‖) ^ (a j / 2) := by
      rw [pointBallGauge, rawPointBallFactor_sqrt a y c (norm_nonneg _)]
    have hq : Real.exp (-2 * Q) ≤ Real.exp (-2 * ∑ j, a j) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ Real.exp (-2 * ∑ j, a j) * pointBallGauge a y c z :=
        mul_le_mul_of_nonneg_right hq (pointBallGauge_nonneg a y c z)
      _ ≤ _ := by rw [hg]; simpa only [mul_assoc] using h

end RepulsiveCoulomb
