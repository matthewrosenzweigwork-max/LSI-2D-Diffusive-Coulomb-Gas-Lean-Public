module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The correctly oriented L1 centering inequality used in the Bjorn transfer
argument: mean-centered oscillation is at most twice oscillation about any
constant. Bjorn2001 printed equation(8) in the opposite orientation; the proof
requires the direction established here. -/
noncomputable section
open MeasureTheory Filter
namespace RepulsiveCoulomb

theorem integral_norm_centered_le_twice {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ) (c : ℝ) :
    (∫ x, ‖f x - ∫ y, f y ∂μ‖ ∂μ) ≤ 2 * ∫ x, ‖f x - c‖ ∂μ := by
  have hg : Integrable (fun x => f x - c) μ := hf.sub (integrable_const c)
  have hmean : ‖(∫ y, f y ∂μ) - c‖ ≤ ∫ x, ‖f x - c‖ ∂μ := by
    have h := norm_integral_le_integral_norm (f := fun x => f x - c) (μ := μ)
    rwa [integral_sub hf (integrable_const c), integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul] at h
  have hpoint (x : X) : ‖f x - ∫ y, f y ∂μ‖ ≤ ‖f x - c‖ + ‖(∫ y, f y ∂μ) - c‖ := by
    have h := norm_sub_le (f x - c) ((∫ y, f y ∂μ) - c)
    simpa only [sub_sub_sub_cancel_right] using h
  have h := integral_mono (hf.sub (integrable_const _)).norm
    (hg.norm.add (integrable_const _)) hpoint
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_add hg.norm (integrable_const _), integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] at h
  linarith

end RepulsiveCoulomb
