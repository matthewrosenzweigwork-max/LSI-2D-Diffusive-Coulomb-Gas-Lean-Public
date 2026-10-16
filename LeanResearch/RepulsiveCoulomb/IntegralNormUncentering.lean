module

public import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-! Uncentering in a finite-measure real Lq norm. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem integral_rpow_uncenter {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (c : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    (∫ x, ‖f x‖ ^ q ∂μ) ^ (1 / q) ≤
      |c| * (μ.real univ) ^ (1 / q) + (∫ x, ‖f x - c‖ ^ q ∂μ) ^ (1 / q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have h := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) (p := ENNReal.ofReal q)
    (memLp_const (μ := μ) c) hp
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 ENNReal.ofReal_ne_top hf,
    lpNorm_const' hp0 ENNReal.ofReal_ne_top,
    lpNorm_eq_integral_norm_rpow_toReal hp0 ENNReal.ofReal_ne_top
      (hf.sub aestronglyMeasurable_const)] at h
  simpa only [ENNReal.toReal_ofReal hq0.le, Pi.sub_apply, one_div, Real.norm_eq_abs] using h

theorem integral_ball_mean_abs_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {S : Set X} (hS : MeasurableSet S)
    (hm : 1 / 2 ≤ μ.real S) {f : X → ℝ} (hf : Integrable f μ) :
    |⨍ x in S, f x ∂μ| ≤ 2 * (∫ x, |f x| ∂μ) := by
  have hmass : 0 < μ.real S := by linarith
  have hn := norm_average_le_average_norm (μ.restrict S) f
  have ht : (∫ x in S, ‖f x‖ ∂μ) ≤ ∫ x, |f x| ∂μ := by
    simpa only [Real.norm_eq_abs] using setIntegral_le_integral hf.norm
      (Eventually.of_forall (fun x => norm_nonneg (f x)))
  have hi : (μ.real S)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hmass).mpr
    linarith
  have hm0 : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg (fun x => abs_nonneg _)
  have hn' : |⨍ x in S, f x ∂μ| ≤ (μ.real S)⁻¹ * (∫ x in S, ‖f x‖ ∂μ) := by
    simpa only [average_eq, smul_eq_mul, Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] using hn
  exact hn'.trans ((mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hmass.le)).trans
    (mul_le_mul_of_nonneg_right hi hm0))

end RepulsiveCoulomb
