module

public import LeanResearch.RepulsiveCoulomb.PointLocalizedMaximal

@[expose] public section

/-! The second, global-energy estimate for each actual local gradient average. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_centered_small_ball_lower {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R r : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (hr : 0 < r) (hrR : r ≤ 2 * R) :
    (rawPointMeasure a y).real (ball c R) ≤
      (rawPointGrowthConstant Q * (2 * R / r) ^ (Q + 2)) *
        (rawPointMeasure a y).real (ball x (5 * r)) := by
  have hsub : ball c R ⊆ ball x (2 * R) := by
    apply ball_subset_ball'
    have hd : dist c x < R := by simpa only [dist_comm] using mem_ball.mp hx
    linarith
  have hg := rawPointMeasure_growth_real ha hQ y x hr ((le_div_iff₀ hr).mpr (by simpa using hrR))
  rw [div_mul_cancel₀ _ hr.ne'] at hg
  have hsmall : (rawPointMeasure a y).real (ball x r) ≤
      (rawPointMeasure a y).real (ball x (5 * r)) :=
    ENNReal.toReal_mono (rawPointMeasure_ball_lt_top ha y x _).ne
      (measure_mono (ball_subset_ball (by linarith)))
  exact (ENNReal.toReal_mono (rawPointMeasure_ball_lt_top ha y x _).ne (measure_mono hsub)).trans
    (hg.trans (mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg (rawPointGrowthConstant_pos Q).le (Real.rpow_nonneg (by positivity) _))))

theorem rawPointMeasure_local_energy_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      (rawPointGrowthConstant Q * (2 * R / dyadicBallRadius (2 * R) n) ^ (Q + 2)) *
        (∫ z in ball c (11 * R), g z ∂rawPointMeasure a y) /
        (rawPointMeasure a y).real (ball c R) := by
  let μ := rawPointMeasure a y
  let r := dyadicBallRadius (2 * R) n
  have hr : 0 < r := dyadicBallRadius_pos (by positivity) n
  have hM : 0 < μ.real (ball x (5 * r)) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y x (by positivity)).ne'
      (rawPointMeasure_ball_lt_top ha y x _).ne
  have hN : 0 < μ.real (ball c R) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne'
      (rawPointMeasure_ball_lt_top ha y c R).ne
  have hi : (∫ z in ball x (5 * r), g z ∂μ) ≤ ∫ z in ball c (11 * R), g z ∂μ :=
    setIntegral_mono_set (rawPointMeasure_continuous_ball_integrable ha y hg c _)
      (Eventually.of_forall hgn) (Eventually.of_forall (dyadic_gradient_ball_subset hR hx n))
  have he : 0 ≤ ∫ z in ball c (11 * R), g z ∂μ := integral_nonneg (fun z => hgn z)
  have hm := rawPointMeasure_centered_small_ball_lower ha hQ y hR hx hr
    (dyadicBallRadius_le (by positivity) n)
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (μ.real (ball x (5 * r)))⁻¹ * (∫ z in ball x (5 * r), g z ∂μ) ≤ _
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_right hi hM.le).trans
  apply (le_div_iff₀ hN).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hM).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm he]

end RepulsiveCoulomb
