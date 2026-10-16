module

public import LeanResearch.RepulsiveCoulomb.MeanRpowCentering

@[expose] public section

/-! Normalized real Lq recentering, with all needed actual moments integrable. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem average_rpow_mean_centering {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hfm : Measurable f) (hf : Integrable f μ) (c : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (hp : Integrable (fun x => ‖f x - c‖ ^ q) μ)
    (hpmean : Integrable (fun x => ‖f x - (⨍ z, f z ∂μ)‖ ^ q) μ) :
    (⨍ x, ‖f x - (⨍ z, f z ∂μ)‖ ^ q ∂μ) ≤
      (2 * (2 : ℝ) ^ q) * (⨍ x, ‖f x - c‖ ^ q ∂μ) := by
  have h := lintegral_rpow_mean_centering μ hfm hf c hq hp
  have hC : 0 ≤ 2 * (2 : ℝ) ^ q := by positivity
  have he : (2 : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ q) = ENNReal.ofReal (2 * (2 : ℝ) ^ q) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hpmean
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ← ofReal_integral_eq_lintegral_ofReal hp
      (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ← ENNReal.ofReal_mul hC] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ENNReal.toReal_ofReal (mul_nonneg hC (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)))] at hr
  conv_lhs => rw [average_eq, smul_eq_mul]
  conv_rhs => arg 2; rw [average_eq, smul_eq_mul]
  calc
    _ ≤ (μ.real univ)⁻¹ * ((2 * (2 : ℝ) ^ q) * ∫ x, ‖f x - c‖ ^ q ∂μ) :=
      mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = _ := by ring

end RepulsiveCoulomb
