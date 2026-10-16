import LeanResearch.RepulsiveCoulomb.PointDyadicEnergy

/-! A pointwise finite localized maximal energy for continuous inputs, and its
actual control of the square-root averages in the Poincare chain. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointLocalMaximalEnergy {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (R : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  rawPointDyadicMaximal a y (10 * R) ((ball c (11 * R)).indicator (fun z => ENNReal.ofReal (g z))) x

theorem pointLocalMaximalEnergy_measurable {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) (R : ℝ)
    {g : ℂ → ℝ} (hg : Continuous g) : Measurable (pointLocalMaximalEnergy a y c R g) :=
  measurable_rawPointDyadicMaximal ha y _ (hg.measurable.ennreal_ofReal.indicator measurableSet_ball)

theorem pointLocalMaximalEnergy_lt_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Continuous g) (x : ℂ) : pointLocalMaximalEnergy a y c R g x < ⊤ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall c (11 * R)).bddAbove_image hg.continuousOn
  apply rawPointDyadicMaximal_lt_top_of_bound ha y (show 0 < 10 * R by positivity)
    (b := ENNReal.ofReal B) ?_ ENNReal.ofReal_lt_top
  intro z
  by_cases hz : z ∈ ball c (11 * R)
  · rw [Set.indicator_of_mem hz]
    exact ENNReal.ofReal_le_ofReal (hB (mem_image_of_mem g (ball_subset_closedBall hz)))
  · rw [Set.indicator_of_notMem hz]
    exact bot_le

theorem pointLocalMaximalEnergy_average_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) (g : ℂ → ℝ) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      (pointLocalMaximalEnergy a y c R g x).toReal := by
  have hr : 0 < 5 * dyadicBallRadius (2 * R) n := by
    have := dyadicBallRadius_pos (show 0 < 2 * R by positivity) n
    positivity
  have h := rawPoint_dyadic_average_le_local_maximal ha y hR hx (fun z => ENNReal.ofReal (g z)) n
  rw [← rawPointKernelAverage_eq ha y hr] at h
  change rawPointKernelAverage a y (5 * dyadicBallRadius (2 * R) n)
    (fun z => ENNReal.ofReal (g z)) x ≤ pointLocalMaximalEnergy a y c R g x at h
  have he := rawPointMeasure_ofReal_average_eq_kernel ha y g hg hgn x (5 * dyadicBallRadius (2 * R) n)
  change ENNReal.ofReal _ = rawPointKernelAverage a y _ (fun z => ENNReal.ofReal (g z)) x at he
  rw [← he] at h
  have ht := ENNReal.toReal_mono (pointLocalMaximalEnergy_lt_top ha y c hR hg x).ne h
  simpa only [ENNReal.toReal_ofReal (average_nonneg hgn)] using ht

theorem pointLocalMaximalEnergy_sqrt_average_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) (g : ℂ → ℝ) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      Real.sqrt (pointLocalMaximalEnergy a y c R g x).toReal :=
  Real.sqrt_le_sqrt (pointLocalMaximalEnergy_average_bound ha y hR hx g hg hgn n)

end RepulsiveCoulomb
