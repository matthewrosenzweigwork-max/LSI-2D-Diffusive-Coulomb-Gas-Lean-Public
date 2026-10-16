import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual Lq recentering from an arbitrary real center to the weighted mean. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem norm_sub_rpow_center_bound {q : ℝ} (hq : 0 ≤ q) (a b c : ℝ) :
    ‖a - b‖ ^ q ≤ (2 : ℝ) ^ q * (‖a - c‖ ^ q + ‖b - c‖ ^ q) := by
  have ht : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (a - c) (b - c)
  rcases le_total ‖a - c‖ ‖b - c‖ with h | h
  · have hb : ‖a - b‖ ≤ 2 * ‖b - c‖ := by linarith
    have hp := Real.rpow_le_rpow (norm_nonneg _) hb hq
    rw [Real.mul_rpow (by norm_num) (norm_nonneg _)] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))
  · have ha : ‖a - b‖ ≤ 2 * ‖a - c‖ := by linarith
    have hp := Real.rpow_le_rpow (norm_nonneg _) ha hq
    rw [Real.mul_rpow (by norm_num) (norm_nonneg _)] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))

theorem weighted_mean_rpow_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (c : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (hp : Integrable (fun x => ‖f x - c‖ ^ q) μ) :
    μ.real univ * ‖(⨍ x, f x ∂μ) - c‖ ^ q ≤ ∫ x, ‖f x - c‖ ^ q ∂μ := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hu : Integrable (fun x => f x - c) μ := hf.sub (integrable_const c)
  have hj := (convexOn_rpow hq).map_average_le
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
    (Eventually.of_forall (fun x => norm_nonneg (f x - c))) hu.norm hp
  have hn := (Real.rpow_le_rpow (norm_nonneg _)
    (norm_average_le_average_norm μ (fun x => f x - c)) hq0).trans hj
  rw [average_fun_sub hf (integrable_const c), average_const] at hn
  have hM : 0 < μ.real univ := measureReal_univ_pos
  calc
    _ ≤ μ.real univ * (⨍ x, ‖f x - c‖ ^ q ∂μ) := mul_le_mul_of_nonneg_left hn hM.le
    _ = _ := by
      rw [average_eq, smul_eq_mul]
      field_simp

theorem lintegral_rpow_mean_centering {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hfm : Measurable f) (hf : Integrable f μ) (c : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (hp : Integrable (fun x => ‖f x - c‖ ^ q) μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x - (⨍ z, f z ∂μ)‖ ^ q) ∂μ) ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ q)) * ∫⁻ x, ENNReal.ofReal (‖f x - c‖ ^ q) ∂μ := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hc : (∫⁻ _x, ENNReal.ofReal (‖(⨍ z, f z ∂μ) - c‖ ^ q) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (‖f x - c‖ ^ q) ∂μ := by
    rw [lintegral_const, ← ofReal_integral_eq_lintegral_ofReal hp
      (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
      ← ENNReal.ofReal_toReal (measure_ne_top μ univ),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm, Measure.real] using weighted_mean_rpow_bound μ hf c hq hp
  have hm : Measurable (fun x => ENNReal.ofReal (‖f x - c‖ ^ q)) :=
    ((Real.continuous_rpow_const hq0).measurable.comp (hfm.sub_const c).norm).ennreal_ofReal
  have h := lintegral_mono (μ := μ) (fun x => ENNReal.ofReal_le_ofReal
    (norm_sub_rpow_center_bound hq0 (f x) (⨍ z, f z ∂μ) c))
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
    ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm] at h
  apply h.trans
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ q) * ((∫⁻ x, ENNReal.ofReal (‖f x - c‖ ^ q) ∂μ) +
        ∫⁻ x, ENNReal.ofReal (‖f x - c‖ ^ q) ∂μ) := mul_le_mul' le_rfl (add_le_add le_rfl hc)
    _ = _ := by rw [mul_add, two_mul, add_mul]

end RepulsiveCoulomb
