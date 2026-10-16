import LeanResearch.RepulsiveCoulomb.RawPointVolumeGrowth
import Mathlib.MeasureTheory.Measure.Prod

/-! Actual local finiteness and measurable moving-ball masses, with uniform
comparison for intersecting equal-radius balls. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_ball_lt_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    rawPointMeasure a y (ball c r) < ⊤ :=
  (measure_mono ball_subset_closedBall).trans_lt (rawPointMeasure_closedBall_lt_top ha y c r)

theorem rawPointMeasure_locallyFinite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : IsLocallyFiniteMeasure (rawPointMeasure a y) := by
  refine ⟨fun c => ⟨ball c 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩⟩
  exact rawPointMeasure_ball_lt_top ha y c 1

theorem measurable_rawPointMeasure_ball {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (r : ℝ) :
    Measurable (fun c : ℂ => rawPointMeasure a y (ball c r)) := by
  letI := rawPointMeasure_locallyFinite ha y
  have hs : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} := by
    exact (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h := measurable_measure_prodMk_left (ν := rawPointMeasure a y) hs
  convert h using 1
  ext c
  congr 1

theorem rawPointMeasure_neighbor_ball_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {x z : ℂ} {r : ℝ} (hr : 0 < r) (hxz : dist z x < r) :
    (rawPointMeasure a y).real (ball z r) ≤
      rawPointDoublingConstant Q * (rawPointMeasure a y).real (ball x r) := by
  have hsub : ball z r ⊆ ball x (2 * r) := by
    apply ball_subset_ball'
    linarith
  have h := (measure_mono hsub).trans (rawPointMeasure_ball_doubling ha hQ y x hr)
  have hfin : ENNReal.ofReal (rawPointDoublingConstant Q) * rawPointMeasure a y (ball x r) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (rawPointMeasure_ball_lt_top ha y x r)).ne
  have ht := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (rawPointDoublingConstant_pos Q).le,
    Measure.real] using ht

end RepulsiveCoulomb
