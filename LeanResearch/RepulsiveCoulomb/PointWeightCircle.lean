module

public import LeanResearch.RepulsiveCoulomb.PointWeightBounds

@[expose] public section

/-! The Euclidean circle-average input for the uniform lower normalization
bound. The logarithmic average is Mathlib's exact planar identity, and
Jensen is applied to actual integrable functions on angular Lebesgue measure.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators ENNReal Topology
namespace RepulsiveCoulomb

theorem circleAverage_exp_ge (f : ℂ → ℝ) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) (he : CircleIntegrable (Real.exp ∘ f) c R) :
    Real.exp (Real.circleAverage f c R) ≤ Real.circleAverage (Real.exp ∘ f) c R := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hμ : μ ≠ 0 := by
    intro h
    have hm := congrArg (fun ν : Measure ℝ ↦ ν Set.univ) h
    apply (ne_of_gt (ENNReal.ofReal_pos.mpr Real.two_pi_pos))
    simpa [μ] using hm
  let _ : NeZero μ := ⟨hμ⟩
  have hj := convexOn_exp.map_average_le (μ := μ) (f := fun θ ↦ f (circleMap c R θ))
    Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ ↦ Set.mem_univ _)) hf.1 he.1
  simpa only [average_eq, μ, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal Real.two_pi_pos.le,
    Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le, Function.comp_def] using hj

theorem log_one_add_le_log_radius_posLog {R t : ℝ} (hR : 1 ≤ R) (ht : 0 ≤ t) :
    Real.log (1 + t) - Real.log 2 ≤ Real.log R + Real.posLog (R⁻¹ * t) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  by_cases htR : t ≤ R
  · have hl := Real.log_le_log (by positivity : 0 < 1 + t)
      (by linarith : 1 + t ≤ 2 * R)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR0.ne'] at hl
    have hp : 0 ≤ Real.posLog (R⁻¹ * t) := Real.posLog_nonneg
    linarith
  · have ht0 : 0 < t := hR0.trans (lt_of_not_ge htR)
    have hl := Real.log_le_log (by positivity : 0 < 1 + t)
      (by linarith : 1 + t ≤ 2 * t)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'] at hl
    calc
      Real.log (1 + t) - Real.log 2 ≤ Real.log t := by linarith
      _ = Real.log R + Real.log (R⁻¹ * t) := by
        rw [Real.log_mul (inv_ne_zero hR0.ne') ht0.ne', Real.log_inv]
        ring
      _ ≤ _ := add_le_add le_rfl (le_max_right 0 (Real.log (R⁻¹ * t)))

theorem circleAverage_log_distance_lower {R : ℝ} (hR : 1 ≤ R) (y : ℂ) :
    Real.log (1 + ‖y‖) - Real.log 2 ≤
      Real.circleAverage (fun z : ℂ ↦ Real.log ‖z - y‖) 0 R := by
  have hR0 : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR0]
  simpa using log_one_add_le_log_radius_posLog hR (norm_nonneg y)

end RepulsiveCoulomb
