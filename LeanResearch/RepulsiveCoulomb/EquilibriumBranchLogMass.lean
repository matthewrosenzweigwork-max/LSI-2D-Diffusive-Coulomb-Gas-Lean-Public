module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The exact positive-logarithm mass that yields the manuscript upper
potential bound `U ≤ 1/2` from `ρ ≤ 1/pi`. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

private theorem equilibrium_radial_log_integral :
    (∫ t in (0 : ℝ)..1, -(t * Real.log t)) = 1 / 4 := by
  let F : ℝ → ℝ := fun t => t ^ 2 / 4 - t * (t * Real.log t) / 2
  have hc : Continuous F := by
    exact (continuous_id.pow 2 |>.div_const 4).sub
      ((continuous_id.mul Real.continuous_mul_log).div_const 2)
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (-(t * Real.log t)) t := by
    intro t ht
    have h := ((hasDerivAt_id t).pow 2 |>.div_const 4).sub
      (((hasDerivAt_id t).mul (Real.hasDerivAt_mul_log ht.1.ne')).div_const 2)
    convert h using 1
    · rfl
    · dsimp
      ring
  have hi : IntervalIntegrable (fun t : ℝ => -(t * Real.log t)) volume 0 1 :=
    Real.continuous_mul_log.neg.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hc.continuousOn hd hi
  simpa [F] using h

private theorem equilibrium_radial_positive_log :
    (fun t : ℝ => t ^ (Module.finrank ℝ ℂ - 1) • max (-Real.log t) 0)
      =ᵐ[volume.restrict (Ioi 0)]
        (Ioo 0 1).indicator (fun t : ℝ => -(t * Real.log t)) := by
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t < 1
  · have hl : Real.log t ≤ 0 := (Real.log_neg ht0 ht1).le
    simp [ht0, ht1, max_eq_left (neg_nonneg.mpr hl)]
  · have hl : 0 ≤ Real.log t := Real.log_nonneg (le_of_not_gt ht1)
    simp [ht1, max_eq_right (neg_nonpos.mpr hl)]

/-- Exact planar integral of the nonnegative singular part of `-log |z|`. -/
theorem integral_equilibriumLogPositive :
    (∫ z : ℂ, equilibriumLogPositive z) = Real.pi / 2 := by
  change (∫ z : ℂ, (fun t : ℝ => max (-Real.log t) 0) ‖z‖) = _
  rw [integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ)
    (fun t : ℝ => max (-Real.log t) 0)]
  have hi : (∫ t in Ioi (0 : ℝ), t ^ (Module.finrank ℝ ℂ - 1) •
      max (-Real.log t) 0) = 1 / 4 := by
    rw [integral_congr_ae equilibrium_radial_positive_log,
      setIntegral_indicator measurableSet_Ioo]
    have hs : Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := inter_eq_right.mpr (fun _ h => h.1)
    rw [hs, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact equilibrium_radial_log_integral
  rw [hi]
  simp [Measure.real]
  ring

/-- Translation/reflection-invariant exact singular mass. -/
theorem integral_equilibriumLogPositive_shift (x : ℂ) :
    (∫ y : ℂ, equilibriumLogPositive (x - y)) = Real.pi / 2 := by
  have he : (fun y : ℂ => equilibriumLogPositive (x - y)) =
      (fun y : ℂ => equilibriumLogPositive (y - x)) := by
    funext y
    simp only [equilibriumLogPositive, equilibriumLogKernel, norm_sub_rev]
  rw [he, integral_sub_right_eq_self, integral_equilibriumLogPositive]

end RepulsiveCoulomb
