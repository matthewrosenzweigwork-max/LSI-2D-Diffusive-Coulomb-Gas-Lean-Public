import LeanResearch.RepulsiveCoulomb.RawPointMeasureScaling

/-! Exact pushforward identities for raw point measures and their restrictions
to the physical observation balls. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem rawPointMeasure_set_scaling {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h)
    {S : Set ℂ} (hS : MeasurableSet S) :
    rawPointMeasure a y S = ENNReal.ofReal (h^2 * h^(∑ j,a j)) *
      rawPointMeasure a (fun j => h⁻¹ • y j) ((fun z : ℂ => h • z) ⁻¹' S) := by
  have hf : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_const.indicator hS
  have ht := rawPointMeasure_lintegral_smul ha y hh (S.indicator 1) hf
  rw [lintegral_indicator_one hS] at ht
  have heq : (fun z : ℂ => S.indicator (1 : ℂ → ℝ≥0∞) (h • z)) =
      ((fun z : ℂ => h • z) ⁻¹' S).indicator 1 := by
    funext z
    rfl
  rw [heq,lintegral_indicator_one (hS.preimage (continuous_const_smul h).measurable)] at ht
  exact ht

theorem rawPointMeasure_eq_smul_map {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h) :
    rawPointMeasure a y = ENNReal.ofReal (h^2 * h^(∑ j,a j)) •
      Measure.map (fun z : ℂ => h • z) (rawPointMeasure a (fun j => h⁻¹ • y j)) := by
  apply Measure.ext
  intro S hS
  rw [Measure.smul_apply,Measure.map_apply (continuous_const_smul h).measurable hS]
  exact rawPointMeasure_set_scaling ha y hh hS

theorem rawPointSquaredMeasure_restrict_scaling {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h) (c : ℂ) (R : ℝ) :
    (rawPointMeasure (fun j => 2*a j) y).restrict (ball c R) =
      ENNReal.ofReal (rawPointLengthScale a h ^ 2) •
        Measure.map (fun z : ℂ => h • z)
          ((rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).restrict (ball (h⁻¹ • c) (R/h))) := by
  rw [rawPointMeasure_eq_smul_map (fun j => mul_nonneg (by norm_num) (ha j)) y hh,
    rawPoint_double_measure_scale a hh,Measure.restrict_smul,
    Measure.restrict_map (continuous_const_smul h).measurable isOpen_ball.measurableSet,
    complex_pos_smul_preimage_ball hh]

theorem rawPointSquaredMeasure_ball_scaling {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h) (c : ℂ) (R : ℝ) :
    (rawPointMeasure (fun j => 2*a j) y).real (ball c R) =
      rawPointLengthScale a h ^ 2 *
        (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).real (ball (h⁻¹ • c) (R/h)) := by
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hm := rawPointMeasure_set_scaling ha2 y hh
    (isOpen_ball.measurableSet : MeasurableSet (ball c R))
  rw [rawPoint_double_measure_scale a hh,complex_pos_smul_preimage_ball hh] at hm
  have hh' := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at hh'
  exact hh'

end RepulsiveCoulomb
