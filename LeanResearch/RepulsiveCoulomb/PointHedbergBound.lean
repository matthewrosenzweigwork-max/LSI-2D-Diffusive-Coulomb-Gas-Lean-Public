module

public import LeanResearch.RepulsiveCoulomb.PointHedbergSeries

@[expose] public section

/-! The full actual-series bound, including all zero cases, followed by the
explicitly conditional pointwise oscillation estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointPoincareSeries_hedberg {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    pointPoincareSeries a y R g x ≤ ENNReal.ofReal
      (5 * Real.sqrt (pointLocalMaximalEnergy a y c R g x).toReal /
        (Real.sqrt (pointLocalMaximalEnergy a y c R g x).toReal /
          Real.sqrt (pointLocalEnergy Q a y c R g)) ^ (1 / (Q + 2))) := by
  by_cases hE : pointLocalEnergy Q a y c R g = 0
  · rw [pointPoincareSeries_zero_of_energy_zero ha hQ y hR hx g hg hgn hE]
    exact bot_le
  by_cases hM : (pointLocalMaximalEnergy a y c R g x).toReal = 0
  · rw [pointPoincareSeries_zero_of_maximal_zero ha y hR hx g hg hgn hM]
    exact bot_le
  exact pointPoincareSeries_hedberg_pos ha hQ y hR hx g hg hgn
    (lt_of_le_of_ne (pointLocalEnergy_nonneg Q a y c R g hgn) (Ne.symm hE))
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM))

theorem pointPoincareSeries_lt_top {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    pointPoincareSeries a y R g x < ⊤ :=
  (pointPoincareSeries_hedberg ha hQ y hR hx g hg hgn).trans_lt ENNReal.ofReal_lt_top

theorem rawPointMeasure_oscillation_le_series {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 ≤ P) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂rawPointMeasure a y))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      ENNReal.ofReal (2 * R * P * (rawPointDoublingConstant Q + rawPointInitialMeanConstant Q)) *
        pointPoincareSeries a y R g x := by
  have h := rawPointMeasure_poincare_chain ha hQ y f g hf hPI c hR hx
  let S := pointPoincareSeries a y R g x
  have he (n : ℕ) : rawPointDoublingConstant Q *
      (P * dyadicBallRadius (2 * R) n *
        Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y)) =
      (2 * R * P * rawPointDoublingConstant Q) * ((1 / 2 : ℝ) ^ n *
        Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y)) := by
    unfold dyadicBallRadius
    ring
  have hD : 0 ≤ 2 * R * P * rawPointDoublingConstant Q := by
    have := (rawPointDoublingConstant_pos Q).le
    positivity
  have hA : 0 ≤ 2 * R * P * rawPointInitialMeanConstant Q := by
    have := (rawPointInitialMeanConstant_pos Q).le
    positivity
  simp_rw [he, ENNReal.ofReal_mul hD] at h
  rw [ENNReal.tsum_mul_left] at h
  have hzero : ENNReal.ofReal (Real.sqrt (⨍ z in ball x (10 * R), g z ∂rawPointMeasure a y)) ≤ S := by
    have hh := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
      Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y))) 0
    simpa only [S, pointPoincareSeries, dyadicBallRadius, pow_zero, one_mul, show 5 * (2 * R) = 10 * R by ring] using hh
  have hi : ENNReal.ofReal (rawPointInitialMeanConstant Q *
      (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂rawPointMeasure a y))) ≤
      ENNReal.ofReal (2 * R * P * rawPointInitialMeanConstant Q) * S := by
    rw [show rawPointInitialMeanConstant Q *
      (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂rawPointMeasure a y)) =
      (2 * R * P * rawPointInitialMeanConstant Q) *
        Real.sqrt (⨍ z in ball x (10 * R), g z ∂rawPointMeasure a y) by ring,
      ENNReal.ofReal_mul hA]
    exact mul_le_mul' le_rfl hzero
  apply h.trans
  change ENNReal.ofReal (2 * R * P * rawPointDoublingConstant Q) * S + _ ≤ _
  calc
    _ ≤ ENNReal.ofReal (2 * R * P * rawPointDoublingConstant Q) * S +
        ENNReal.ofReal (2 * R * P * rawPointInitialMeanConstant Q) * S := add_le_add le_rfl hi
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add hD hA]
      congr 2
      ring

end RepulsiveCoulomb
