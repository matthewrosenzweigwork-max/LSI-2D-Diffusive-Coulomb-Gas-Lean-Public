import LeanResearch.RepulsiveCoulomb.IntegralNormUncentering
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Converting a centered local Sobolev bound on a half-mass region into an
uncentered integral norm, with every normalization accounted for. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem setIntegral_le_setAverage {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {S : Set X} (hm : 0 < μ.real S)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∫ x in S, f x ∂μ) ≤ ⨍ x in S, f x ∂μ := by
  have hi : 1 ≤ (μ.real S)⁻¹ := (one_le_inv₀ hm).mpr (measureReal_le_one)
  simpa only [average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, one_mul] using
    mul_le_mul_of_nonneg_right hi (integral_nonneg hf : 0 ≤ ∫ x in S, f x ∂μ)

theorem half_mass_average_le_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {S : Set X} (hm : 1 / 2 ≤ μ.real S)
    {f : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (⨍ x in S, f x ∂μ) ≤ 2 * (∫ x, f x ∂μ) := by
  have hp : 0 < μ.real S := by linarith
  have hi : (μ.real S)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  have ht := setIntegral_le_integral hf (Eventually.of_forall hf0) (s := S)
  simp only [average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  exact (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hp.le)).trans
    (mul_le_mul_of_nonneg_right hi (integral_nonneg hf0))

theorem local_sobolev_uncentered_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {S T : Set X} (hS : MeasurableSet S)
    (hSm : 1 / 2 ≤ μ.real S) (hTm : 1 / 2 ≤ μ.real T)
    {f e : X → ℝ} (hf : Integrable f μ) (he : Integrable e μ)
    (he0 : ∀ x, 0 ≤ e x) {q H : ℝ} (hq : 1 ≤ q) (hH : 0 ≤ H)
    (hlocal : (⨍ x in S, ‖f x - (⨍ z in S, f z ∂μ)‖ ^ q ∂μ) ^ (1 / q) ≤
      H * Real.sqrt (⨍ x in T, e x ∂μ)) :
    (∫ x in S, ‖f x‖ ^ q ∂μ) ^ (1 / q) ≤
      2 * (∫ x, |f x| ∂μ) + 2 * H * Real.sqrt (∫ x, e x ∂μ) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hSp : 0 < μ.real S := by linarith
  let c : ℝ := ⨍ z in S, f z ∂μ
  have ht := integral_rpow_uncenter (μ.restrict S) hf.aestronglyMeasurable.restrict c hq
  have hpow : (μ.real S) ^ (1 / q) ≤ 1 :=
    Real.rpow_le_one (measureReal_nonneg) (measureReal_le_one) (by positivity)
  have hmean := integral_ball_mean_abs_le μ hS hSm hf
  have hcenter : (∫ x in S, ‖f x - c‖ ^ q ∂μ) ^ (1 / q) ≤
      (⨍ x in S, ‖f x - c‖ ^ q ∂μ) ^ (1 / q) :=
    Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
      (setIntegral_le_setAverage μ hSp _ (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)
  have havg := half_mass_average_le_integral μ hTm he he0
  have hsqrt : Real.sqrt (⨍ x in T, e x ∂μ) ≤ 2 * Real.sqrt (∫ x, e x ∂μ) := by
    calc
      _ ≤ Real.sqrt (2 * (∫ x, e x ∂μ)) := Real.sqrt_le_sqrt havg
      _ = Real.sqrt 2 * Real.sqrt (∫ x, e x ∂μ) := Real.sqrt_mul (by norm_num) _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt (2 : ℝ) ≤ 2) (Real.sqrt_nonneg _)
  have hcen := hcenter.trans (hlocal.trans (mul_le_mul_of_nonneg_left hsqrt hH))
  have hmean' : |c| * (μ.real S) ^ (1 / q) ≤ 2 * (∫ x, |f x| ∂μ) :=
    (mul_le_mul_of_nonneg_left hpow (abs_nonneg c)).trans (by simpa only [mul_one, c] using hmean)
  have ht' : (∫ x in S, ‖f x‖ ^ q ∂μ) ^ (1 / q) ≤
      |c| * (μ.real S) ^ (1 / q) + (∫ x in S, ‖f x - c‖ ^ q ∂μ) ^ (1 / q) := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using ht
  nlinarith only [ht', hmean', hcen]

end RepulsiveCoulomb
