module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! A configuration-free one-dimensional logarithmic lower bound. It is intended
as an additional analytic input for uniform radial path barriers; no global
uniformization or strong A-infinity conclusion is asserted in this module. -/
noncomputable section
open Set MeasureTheory Real
namespace RepulsiveCoulomb

theorem interval_log_distance_formula (d : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.log |t - d|) =
      (1 - d) * Real.log (1 - d) + d * Real.log d - 1 := by
  simp only [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_right, integral_log]
  simp only [zero_sub, Real.log_neg_eq_log]
  ring

theorem interval_log_distance_lower_small {d : ℝ} (hd : 0 ≤ d) (hd2 : d ≤ 2) :
    -2 ≤ ∫ t in (0 : ℝ)..1, Real.log |t - d| := by
  rw [interval_log_distance_formula]
  by_cases h : d ≤ 1
  · have h0 := Real.self_sub_one_le_mul_log hd
    have h1 := Real.self_sub_one_le_mul_log (show 0 ≤ 1 - d by linarith)
    linarith
  · have h1 : 1 ≤ d := (lt_of_not_ge h).le
    have hv : (d - 1) * Real.log (d - 1) ≤ 0 :=
      Real.mul_log_nonpos (by linarith) (by linarith)
    have he : (1 - d) * Real.log (1 - d) = -((d - 1) * Real.log (d - 1)) := by
      rw [show 1 - d = -(d - 1) by ring, Real.log_neg_eq_log]
      ring
    rw [he]
    have := Real.mul_log_nonneg h1
    linarith

theorem interval_log_distance_uniform_lower {d : ℝ} (hd : 0 ≤ d) :
    Real.log (1 + d) - 4 ≤ ∫ t in (0 : ℝ)..1, Real.log |t - d| := by
  by_cases hd2 : d ≤ 2
  · have h := interval_log_distance_lower_small hd hd2
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + d by linarith)
    linarith
  · have h2 : 2 ≤ d := (lt_of_not_ge hd2).le
    have hcont : ContinuousOn (fun t : ℝ => Real.log |t - d|) (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht
        exact abs_ne_zero.mpr (by linarith [ht.2])
    have hi : IntervalIntegrable (fun t : ℝ => Real.log |t - d|) volume 0 1 :=
      hcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
    have hcomp : Real.log ((1 + d) / 3) ≤ ∫ t in (0 : ℝ)..1, Real.log |t - d| := by
      have hm := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log ((1 + d) / 3)) volume 0 1)
        hi (fun t ht => ?_)
      · simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hm
      · apply Real.log_le_log (by positivity)
        rw [abs_of_nonpos (by linarith [ht.2])]
        linarith [ht.2]
    rw [Real.log_div (by linarith) (by norm_num)] at hcomp
    have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith

end RepulsiveCoulomb
