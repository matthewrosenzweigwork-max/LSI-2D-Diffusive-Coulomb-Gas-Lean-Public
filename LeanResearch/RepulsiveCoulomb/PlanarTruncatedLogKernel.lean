import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.Integral

/-! Exact L1 control of the truncated planar logarithmic-force kernel.
The radial change of variables is Mathlib's Haar-to-sphere theorem. The
singular value at zero is irrelevant to integration and no divergent
Bochner integral is used without an integrability proof.
-/
noncomputable section
open MeasureTheory Set Metric Real
open scoped ENNReal
namespace RepulsiveCoulomb

def truncatedLogKernel (R : ℝ) (z : ℂ) : ℝ :=
  if ‖z‖ < R then ‖z‖⁻¹ else 0

theorem truncatedLogKernel_nonneg (R : ℝ) (z : ℂ) : 0 ≤ truncatedLogKernel R z := by
  unfold truncatedLogKernel
  split_ifs <;> positivity

theorem truncatedLogKernel_measurable (R : ℝ) : Measurable (truncatedLogKernel R) := by
  exact ((continuous_norm.measurable.inv).ite
    (measurableSet_lt continuous_norm.measurable measurable_const) measurable_const)

private theorem radial_truncatedLogKernel {R : ℝ} :
    (fun t : ℝ ↦ t ^ (Module.finrank ℝ ℂ - 1) • (if t < R then t⁻¹ else 0))
      =ᵐ[volume.restrict (Ioi 0)] (Ioo 0 R).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
  have ht0 : 0 < t := ht
  by_cases htR : t < R
  · simp [htR, ht0, ht0.ne', Set.indicator_of_mem]
  · simp [htR, Set.indicator_of_notMem]

theorem truncatedLogKernel_integrable (R : ℝ) : Integrable (truncatedLogKernel R) := by
  change Integrable (fun z : ℂ ↦ (fun t : ℝ ↦ if t < R then t⁻¹ else 0) ‖z‖)
  apply (integrable_fun_norm_addHaar (E := ℂ) (F := ℝ) (volume : Measure ℂ)
    (f := fun t : ℝ ↦ if t < R then t⁻¹ else 0)).mpr
  have hi0 : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioo 0 R) volume :=
    integrableOn_const (by simp)
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hi0
  exact hi.integrableOn.congr radial_truncatedLogKernel.symm

theorem integral_truncatedLogKernel {R : ℝ} (hR : 0 ≤ R) :
    ∫ z : ℂ, truncatedLogKernel R z = 2 * Real.pi * R := by
  change (∫ z : ℂ, (fun t : ℝ ↦ if t < R then t⁻¹ else 0) ‖z‖) = _
  rw [integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ)
    (fun t : ℝ ↦ if t < R then t⁻¹ else 0)]
  have hi : (∫ t in Ioi (0 : ℝ), t ^ (Module.finrank ℝ ℂ - 1) •
      (if t < R then t⁻¹ else 0)) = R := by
    rw [integral_congr_ae radial_truncatedLogKernel,
      setIntegral_indicator measurableSet_Ioo]
    have hs : Ioi (0 : ℝ) ∩ Ioo 0 R = Ioo 0 R := inter_eq_right.mpr (fun _ h ↦ h.1)
    rw [hs, setIntegral_const]
    simp [Measure.real, hR]
  rw [hi]
  simp [Measure.real, mul_assoc]

theorem truncatedLogKernel_shift_integrable (R : ℝ) (y : ℂ) :
    Integrable (fun z : ℂ ↦ truncatedLogKernel R (z - y)) :=
  (truncatedLogKernel_integrable R).comp_sub_right y

theorem integral_truncatedLogKernel_shift {R : ℝ} (hR : 0 ≤ R) (y : ℂ) :
    ∫ z : ℂ, truncatedLogKernel R (z - y) = 2 * Real.pi * R := by
  rw [integral_sub_right_eq_self]
  exact integral_truncatedLogKernel hR

end RepulsiveCoulomb
