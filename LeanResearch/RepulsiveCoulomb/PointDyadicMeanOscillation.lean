module

public import LeanResearch.RepulsiveCoulomb.PointGlobalMeanOscillation

@[expose] public section

/-! Dyadic telescoping directly in terms of mean-centered L1 oscillation.
These are actual identities and inequalities, with no Poincare hypothesis. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_dyadic_mean_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal ‖f c - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      ∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant Q *
        ⨍ x in ball c (dyadicBallRadius R n),
          ‖f x - (⨍ z in ball c (dyadicBallRadius R n), f z ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) := by
  let μ := rawPointMeasure a y
  let u : ℕ → ℝ := fun n => ⨍ z in ball c (dyadicBallRadius R n), f z ∂μ
  have hlim : Tendsto u atTop (𝓝 (f c)) :=
    (rawPointMeasure_average_tendsto ha y f hf c).comp (dyadicBallRadius_tendsto hR)
  have hstep (n : ℕ) : ‖u (n + 1) - u n‖ ≤ rawPointDoublingConstant Q *
      ⨍ x in ball c (dyadicBallRadius R n),
        ‖f x - (⨍ z in ball c (dyadicBallRadius R n), f z ∂μ)‖ ∂μ := by
    have hr := dyadicBallRadius_pos hR n
    have hs := dyadicBallRadius_pos hR (n + 1)
    have he : 2 * dyadicBallRadius R (n + 1) = dyadicBallRadius R n := by
      simp only [dyadicBallRadius, pow_succ]
      ring
    have hST : ball c (dyadicBallRadius R (n + 1)) ⊆ ball c (dyadicBallRadius R n) :=
      ball_subset_ball (by linarith)
    have h := norm_nested_average_difference_le μ hST
      (rawPointMeasure_ball_pos ha y c hs).ne' (rawPointMeasure_ball_lt_top ha y c _).ne
      (rawPointMeasure_ball_pos ha y c hr).ne' (rawPointMeasure_ball_lt_top ha y c _).ne
      (rawPointMeasure_continuous_ball_integrable ha y hf c _)
    have hmass := rawPointMeasure_doubling_real ha hQ y c hs
    rw [he] at hmass
    have hpos : 0 < μ.real (ball c (dyadicBallRadius R (n + 1))) :=
      ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hs).ne' (rawPointMeasure_ball_lt_top ha y c _).ne
    have hratio : μ.real (ball c (dyadicBallRadius R n)) /
        μ.real (ball c (dyadicBallRadius R (n + 1))) ≤ rawPointDoublingConstant Q :=
      (div_le_iff₀ hpos).mpr hmass
    exact h.trans (mul_le_mul_of_nonneg_right hratio
      (average_nonneg (fun x => norm_nonneg _)))
  have ht := edist_le_tsum_of_edist_le_of_tendsto₀
    (fun n : ℕ => ENNReal.ofReal (rawPointDoublingConstant Q *
      ⨍ x in ball c (dyadicBallRadius R n),
        ‖f x - (⨍ z in ball c (dyadicBallRadius R n), f z ∂μ)‖ ∂μ))
    (fun n => by simpa only [edist_dist, dist_eq_norm'] using ENNReal.ofReal_le_ofReal (hstep n)) hlim
  simpa only [u, dyadicBallRadius, pow_zero, one_mul, edist_dist, dist_eq_norm'] using ht

theorem rawPointMeasure_initial_mean_difference_centered {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ‖(⨍ z in ball c R, f z ∂rawPointMeasure a y) - (⨍ z in ball x (2 * R), f z ∂rawPointMeasure a y)‖ ≤
      rawPointInitialMeanConstant Q * ⨍ z in ball x (2 * R),
        ‖f z - (⨍ w in ball x (2 * R), f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y := by
  have h2R : 0 < 2 * R := by positivity
  have hsub : ball c R ⊆ ball x (2 * R) := by
    apply ball_subset_ball'
    have hcx : dist c x < R := by simpa only [dist_comm] using mem_ball.mp hx
    linarith
  have h := norm_nested_average_difference_le (rawPointMeasure a y) hsub
    (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
    (rawPointMeasure_ball_pos ha y x h2R).ne' (rawPointMeasure_ball_lt_top ha y x (2 * R)).ne
    (rawPointMeasure_continuous_ball_integrable ha y hf x (2 * R))
  have hpos : 0 < (rawPointMeasure a y).real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne' (rawPointMeasure_ball_lt_top ha y c R).ne
  have hr : (rawPointMeasure a y).real (ball x (2 * R)) / (rawPointMeasure a y).real (ball c R) ≤
      rawPointInitialMeanConstant Q :=
    (div_le_iff₀ hpos).mpr (rawPointMeasure_shifted_ball_real ha hQ y c hR hx)
  exact h.trans (mul_le_mul_of_nonneg_right hr (average_nonneg (fun z => norm_nonneg _)))

theorem rawPointMeasure_global_dyadic_mean_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      (∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant Q *
        ⨍ z in ball x (dyadicBallRadius (2 * R) n),
          ‖f z - (⨍ w in ball x (dyadicBallRadius (2 * R) n), f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y)) +
      ENNReal.ofReal (rawPointInitialMeanConstant Q *
        ⨍ z in ball x (2 * R), ‖f z - (⨍ w in ball x (2 * R), f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) := by
  let A := ⨍ z in ball c R, f z ∂rawPointMeasure a y
  let B := ⨍ z in ball x (2 * R), f z ∂rawPointMeasure a y
  have ht : ‖f x - A‖ ≤ ‖f x - B‖ + ‖A - B‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x - B) (A - B)
  calc
    _ ≤ ENNReal.ofReal (‖f x - B‖ + ‖A - B‖) := ENNReal.ofReal_le_ofReal ht
    _ = ENNReal.ofReal ‖f x - B‖ + ENNReal.ofReal ‖A - B‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := add_le_add (rawPointMeasure_dyadic_mean_oscillation ha hQ y f hf x (by positivity))
      (ENNReal.ofReal_le_ofReal (rawPointMeasure_initial_mean_difference_centered ha hQ y f hf c hR hx))

end RepulsiveCoulomb
