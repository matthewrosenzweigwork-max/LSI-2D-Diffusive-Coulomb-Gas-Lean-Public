import LeanResearch.RepulsiveCoulomb.PointDyadicOscillation

/-! Comparison with the mean on a fixed original ball, closing the initial
term in the pointwise dyadic oscillation representation. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointInitialMeanConstant (Q : ℝ) : ℝ := rawPointGrowthConstant Q * (3 : ℝ) ^ (Q + 2)

theorem rawPointInitialMeanConstant_pos (Q : ℝ) : 0 < rawPointInitialMeanConstant Q :=
  mul_pos (rawPointGrowthConstant_pos Q) (Real.rpow_pos_of_pos (by norm_num) _)

theorem rawPointMeasure_growth_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 1 ≤ s) :
    (rawPointMeasure a y).real (ball c (s * r)) ≤
      (rawPointGrowthConstant Q * s ^ (Q + 2)) * (rawPointMeasure a y).real (ball c r) := by
  have h := rawPointMeasure_volume_growth ha hQ y c hr hs
  simp only [rawPointMeasure_closedBall_eq_ball] at h
  have hfin : ENNReal.ofReal (rawPointGrowthConstant Q * s ^ (Q + 2)) *
      rawPointMeasure a y (ball c r) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (rawPointMeasure_ball_lt_top ha y c r)).ne
  have ht := ENNReal.toReal_mono hfin h
  have hC : 0 ≤ rawPointGrowthConstant Q * s ^ (Q + 2) :=
    mul_nonneg (rawPointGrowthConstant_pos Q).le (Real.rpow_nonneg (zero_le_one.trans hs) _)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ht

theorem rawPointMeasure_shifted_ball_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    (rawPointMeasure a y).real (ball x (2 * R)) ≤
      rawPointInitialMeanConstant Q * (rawPointMeasure a y).real (ball c R) := by
  have hsub : ball x (2 * R) ⊆ ball c (3 * R) := by
    apply ball_subset_ball'
    have hxc := mem_ball.mp hx
    linarith
  have hm := ENNReal.toReal_mono (rawPointMeasure_ball_lt_top ha y c (3 * R)).ne (measure_mono hsub)
  exact hm.trans (rawPointMeasure_growth_real ha hQ y c hR (by norm_num : (1 : ℝ) ≤ 3))

theorem rawPointMeasure_initial_mean_difference {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ‖(⨍ z in ball c R, f z ∂rawPointMeasure a y) - (⨍ z in ball x (2 * R), f z ∂rawPointMeasure a y)‖ ≤
      rawPointInitialMeanConstant Q * ⨍ z in ball x (2 * R), ⨍ w in ball x (2 * R),
        ‖f z - f w‖ ∂rawPointMeasure a y ∂rawPointMeasure a y := by
  have h2R : 0 < 2 * R := by positivity
  have hsub : ball c R ⊆ ball x (2 * R) := by
    apply ball_subset_ball'
    have hcx : dist c x < R := by simpa only [dist_comm] using mem_ball.mp hx
    linarith
  have h := norm_nested_average_difference_le_double (rawPointMeasure a y) hsub
    (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
    (rawPointMeasure_ball_pos ha y x h2R).ne' (rawPointMeasure_ball_lt_top ha y x (2 * R)).ne
    (rawPointMeasure_continuous_ball_integrable ha y hf x (2 * R))
  have hpos : 0 < (rawPointMeasure a y).real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
  have hr : (rawPointMeasure a y).real (ball x (2 * R)) / (rawPointMeasure a y).real (ball c R) ≤
      rawPointInitialMeanConstant Q :=
    (div_le_iff₀ hpos).mpr (rawPointMeasure_shifted_ball_real ha hQ y c hR hx)
  exact h.trans (mul_le_mul_of_nonneg_right hr (average_nonneg (fun z => average_nonneg (fun w => norm_nonneg _))))

theorem rawPointMeasure_global_dyadic_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      (∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant Q *
        ⨍ z in ball x (dyadicBallRadius (2 * R) n), ⨍ w in ball x (dyadicBallRadius (2 * R) n),
          ‖f z - f w‖ ∂rawPointMeasure a y ∂rawPointMeasure a y)) +
      ENNReal.ofReal (rawPointInitialMeanConstant Q *
        ⨍ z in ball x (2 * R), ⨍ w in ball x (2 * R), ‖f z - f w‖ ∂rawPointMeasure a y ∂rawPointMeasure a y) := by
  let A := ⨍ z in ball c R, f z ∂rawPointMeasure a y
  let B := ⨍ z in ball x (2 * R), f z ∂rawPointMeasure a y
  have ht : ‖f x - A‖ ≤ ‖f x - B‖ + ‖A - B‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x - B) (A - B)
  calc
    _ ≤ ENNReal.ofReal (‖f x - B‖ + ‖A - B‖) := ENNReal.ofReal_le_ofReal ht
    _ = ENNReal.ofReal ‖f x - B‖ + ENNReal.ofReal ‖A - B‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := add_le_add (rawPointMeasure_dyadic_oscillation ha hQ y f hf x (by positivity))
      (ENNReal.ofReal_le_ofReal (rawPointMeasure_initial_mean_difference ha hQ y f hf c hR hx))

end RepulsiveCoulomb
