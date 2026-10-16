module

public import LeanResearch.RepulsiveCoulomb.PointMeasureAverage
public import LeanResearch.RepulsiveCoulomb.WeightedDoubleOscillation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! An actual dyadic oscillation representation for the raw point measure.
The right side contains genuine double averages; replacing those by gradient
bounds is the separate, still-open David--Semmes step. Infinite sums are ENNReal,
so no summability or hidden pointwise finiteness is assumed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def dyadicBallRadius (R : ℝ) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * R

theorem dyadicBallRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < dyadicBallRadius R n := by
  unfold dyadicBallRadius
  positivity

theorem dyadicBallRadius_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (dyadicBallRadius R) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (dyadicBallRadius_pos hR)⟩
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * R) atTop (𝓝 (0 : ℝ))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const R

theorem rawPointMeasure_doubling_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (rawPointMeasure a y).real (ball c (2 * r)) ≤
      rawPointDoublingConstant Q * (rawPointMeasure a y).real (ball c r) := by
  have hfin : ENNReal.ofReal (rawPointDoublingConstant Q) * rawPointMeasure a y (ball c r) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (rawPointMeasure_ball_lt_top ha y c r)).ne
  have h := ENNReal.toReal_mono hfin (rawPointMeasure_ball_doubling ha hQ y c hr)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (rawPointDoublingConstant_pos Q).le,
    Measure.real] using h

theorem rawPointMeasure_dyadic_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal ‖f c - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      ∑' n : ℕ, ENNReal.ofReal (rawPointDoublingConstant Q *
        ⨍ x in ball c (dyadicBallRadius R n), ⨍ z in ball c (dyadicBallRadius R n),
          ‖f x - f z‖ ∂rawPointMeasure a y ∂rawPointMeasure a y) := by
  let μ := rawPointMeasure a y
  let u : ℕ → ℝ := fun n => ⨍ z in ball c (dyadicBallRadius R n), f z ∂μ
  have hlim : Tendsto u atTop (𝓝 (f c)) :=
    (rawPointMeasure_average_tendsto ha y f hf c).comp (dyadicBallRadius_tendsto hR)
  have hstep (n : ℕ) : ‖u (n + 1) - u n‖ ≤ rawPointDoublingConstant Q *
      ⨍ x in ball c (dyadicBallRadius R n), ⨍ z in ball c (dyadicBallRadius R n),
        ‖f x - f z‖ ∂μ ∂μ := by
    have hr := dyadicBallRadius_pos hR n
    have hs := dyadicBallRadius_pos hR (n + 1)
    have he : 2 * dyadicBallRadius R (n + 1) = dyadicBallRadius R n := by
      simp only [dyadicBallRadius, pow_succ]
      ring
    have hST : ball c (dyadicBallRadius R (n + 1)) ⊆ ball c (dyadicBallRadius R n) :=
      ball_subset_ball (by linarith)
    have h := norm_nested_average_difference_le_double μ hST
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
      (average_nonneg (fun x => average_nonneg (fun z => norm_nonneg _))))
  have ht := edist_le_tsum_of_edist_le_of_tendsto₀
    (fun n : ℕ => ENNReal.ofReal (rawPointDoublingConstant Q *
      ⨍ x in ball c (dyadicBallRadius R n), ⨍ z in ball c (dyadicBallRadius R n),
        ‖f x - f z‖ ∂μ ∂μ))
    (fun n => by simpa only [edist_dist, dist_eq_norm'] using ENNReal.ofReal_le_ofReal (hstep n)) hlim
  simpa only [u, dyadicBallRadius, pow_zero, one_mul, edist_dist, dist_eq_norm'] using ht

end RepulsiveCoulomb
