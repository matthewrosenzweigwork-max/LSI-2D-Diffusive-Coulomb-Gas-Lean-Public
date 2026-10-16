module

public import LeanResearch.RepulsiveCoulomb.PlanarLadyzhenskaya
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-! Exact finite-real norm/integral identities used in the annular estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem lpNorm_two_eq_sqrt_integral {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) {v : X → E} (hv : AEStronglyMeasurable v μ) :
    lpNorm v 2 μ = Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hv]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow]

theorem lpNorm_four_sq_eq_sqrt_integral {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) {v : X → E} (hv : AEStronglyMeasurable v μ) :
    lpNorm v 4 μ ^ 2 = Real.sqrt (∫ x, ‖v x‖ ^ 4 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hv]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [← Real.rpow_mul_natCast (show 0 ≤ ∫ x, ‖v x‖ ^ 4 ∂μ from integral_nonneg (fun x => pow_nonneg (norm_nonneg _) 4)) (1 / 4) 2, Real.sqrt_eq_rpow]
  norm_num

theorem real_norm_fourth (t : ℝ) : ‖t‖ ^ 4 = t ^ 4 := by
  rw [Real.norm_eq_abs]
  calc
    |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
    _ = (t ^ 2) ^ 2 := by rw [sq_abs]
    _ = t ^ 4 := by ring

end RepulsiveCoulomb
