module

public import LeanResearch.RepulsiveCoulomb.PointAveragingFubini
public import LeanResearch.RepulsiveCoulomb.PointMeasureAverage

@[expose] public section

/-! The moving-ball kernel estimate in literal normalized-average form. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_ofReal_average_eq_kernel {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (g : ℂ → ℝ) (hg : Continuous g)
    (hn : ∀ z, 0 ≤ g z) (x : ℂ) (r : ℝ) :
    ENNReal.ofReal (⨍ z in ball x r, g z ∂rawPointMeasure a y) =
      ∫⁻ z, ENNReal.ofReal (rawPointAveragingKernel a y r x z) * ENNReal.ofReal (g z)
        ∂rawPointMeasure a y := by
  let μ := rawPointMeasure a y
  let M := μ.real (ball x r)
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hI := rawPointMeasure_continuous_ball_integrable ha y hg x r
  have he : (fun z => ENNReal.ofReal (rawPointAveragingKernel a y r x z) * ENNReal.ofReal (g z)) =
      (ball x r).indicator (fun z => ENNReal.ofReal M⁻¹ * ENNReal.ofReal (g z)) := by
    funext z
    by_cases hz : z ∈ ball x r
    · simp only [rawPointAveragingKernel, mem_ball.mp hz, ite_true, Set.indicator_of_mem hz]
      rfl
    · have hnot : ¬dist z x < r := hz
      simp only [rawPointAveragingKernel, if_neg hnot, ENNReal.ofReal_zero, zero_mul,
        Set.indicator_of_notMem hz]
  rw [he, lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change ENNReal.ofReal (M⁻¹ * ∫ z in ball x r, g z ∂μ) = _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hM),
    ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hn)]

theorem rawPointMeasure_average_fubini_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ 4 * R)
    (g : ℂ → ℝ) (hg : Continuous g) (hn : ∀ z, 0 ≤ g z) :
    (∫⁻ x in ball c R, ENNReal.ofReal (⨍ z in ball x r, g z ∂rawPointMeasure a y) ∂rawPointMeasure a y) ≤
      ENNReal.ofReal (rawPointDoublingConstant Q) *
        ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y := by
  simp_rw [rawPointMeasure_ofReal_average_eq_kernel ha y g hg hn]
  exact rawPointAveragingKernel_fubini_bound ha hQ y c hr hrR (fun z => ENNReal.ofReal (g z))
    hg.measurable.ennreal_ofReal

end RepulsiveCoulomb
