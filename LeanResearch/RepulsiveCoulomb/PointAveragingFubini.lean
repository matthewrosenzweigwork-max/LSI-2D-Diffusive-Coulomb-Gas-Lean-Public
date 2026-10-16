module

public import LeanResearch.RepulsiveCoulomb.PointAveragingKernel

@[expose] public section

/-! The fully quantitative Tonelli step for moving-ball averages of the actual
raw point measure. This establishes Bjorn's averaging mechanism independently
of the still-open David--Semmes oscillation inequality. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointAveragingKernel_lintegral_le {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (rawPointAveragingKernel a y r x z) ∂rawPointMeasure a y) ≤
      ENNReal.ofReal (rawPointDoublingConstant Q) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (rawPointAveragingKernel_integrable ha hQ y hr z)
    (Eventually.of_forall (fun x => rawPointAveragingKernel_nonneg a y r x z))]
  exact ENNReal.ofReal_le_ofReal (rawPointAveragingKernel_integral_le ha hQ y hr z)

theorem rawPointAveragingKernel_localized {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ 4 * R) (z : ℂ) :
    (∫⁻ x in ball c R, ENNReal.ofReal (rawPointAveragingKernel a y r x z) ∂rawPointMeasure a y) ≤
      (ball c (5 * R)).indicator (fun _ => ENNReal.ofReal (rawPointDoublingConstant Q)) z := by
  by_cases hz : z ∈ ball c (5 * R)
  · rw [Set.indicator_of_mem hz]
    exact (setLIntegral_le_lintegral (ball c R) (fun x => ENNReal.ofReal (rawPointAveragingKernel a y r x z))).trans
      (rawPointAveragingKernel_lintegral_le ha hQ y hr z)
  · rw [Set.indicator_of_notMem hz]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    have hnot : ¬dist z x < r := by
      intro hzx
      apply hz
      apply mem_ball.mpr
      have hxc := mem_ball.mp hx
      have ht := dist_triangle z x c
      linarith
    simp only [rawPointAveragingKernel, if_neg hnot, ENNReal.ofReal_zero, Pi.zero_apply]

theorem rawPointAveragingKernel_fubini_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ 4 * R)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ball c R, ∫⁻ z, ENNReal.ofReal (rawPointAveragingKernel a y r x z) * g z
      ∂rawPointMeasure a y ∂rawPointMeasure a y) ≤
      ENNReal.ofReal (rawPointDoublingConstant Q) * ∫⁻ z in ball c (5 * R), g z ∂rawPointMeasure a y := by
  letI := rawPointMeasure_locallyFinite ha y
  have hj : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (rawPointAveragingKernel a y r p.1 p.2) * g p.2) :=
    (measurable_rawPointAveragingKernel ha y r).ennreal_ofReal.mul (hg.comp measurable_snd)
  rw [lintegral_lintegral_swap hj.aemeasurable]
  calc
    _ = ∫⁻ z, (∫⁻ x in ball c R, ENNReal.ofReal (rawPointAveragingKernel a y r x z)
        ∂rawPointMeasure a y) * g z ∂rawPointMeasure a y := by
      apply lintegral_congr
      intro z
      apply lintegral_mul_const
      exact ((measurable_rawPointAveragingKernel ha y r).comp
        (measurable_id.prodMk (measurable_const (a := z)))).ennreal_ofReal
    _ ≤ ∫⁻ z, (ball c (5 * R)).indicator (fun _ => ENNReal.ofReal (rawPointDoublingConstant Q)) z * g z
        ∂rawPointMeasure a y := by
      apply lintegral_mono
      intro z
      exact mul_le_mul' (rawPointAveragingKernel_localized ha hQ y c hr hrR z) le_rfl
    _ = _ := by
      have he : (fun z => (ball c (5 * R)).indicator (fun _ => ENNReal.ofReal (rawPointDoublingConstant Q)) z * g z) =
          (ball c (5 * R)).indicator (fun z => ENNReal.ofReal (rawPointDoublingConstant Q) * g z) := by
        funext z
        by_cases hz : z ∈ ball c (5 * R) <;> simp [hz]
      rw [he, lintegral_indicator measurableSet_ball,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end RepulsiveCoulomb
