import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircularRegularization
import LeanResearch.RepulsiveCoulomb.PointWeightAnnularNormalization

/-! Exact radial calculation for the unit-disk logarithmic potential in
manuscript Lemma 3.3. The planar identification is supplied separately. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

/-- The exact unit-disk logarithmic potential as a function of distance. -/
def unitDiskLogProfile (t : ℝ) : ℝ :=
  if t ≤ 1 then (t ^ 2 - 1) / 2 else Real.log t

theorem integral_radius_mul_log {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, r * Real.log r) =
      t ^ 2 * Real.log t / 2 - t ^ 2 / 4 := by
  let F : ℝ → ℝ := fun r => r * (r * Real.log r) / 2 - r ^ 2 / 4
  have hc : Continuous F := by
    exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).sub
      (continuous_id.pow 2 |>.div_const 4)
  have hd : ∀ r ∈ Ioo (0 : ℝ) t, HasDerivAt F (r * Real.log r) r := by
    intro r hr
    have h := (((hasDerivAt_id r).mul (Real.hasDerivAt_mul_log hr.1.ne')).div_const 2).sub
      ((hasDerivAt_id r).pow 2 |>.div_const 4)
    convert h using 1
    · rfl
    · dsimp
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn hd
    (Real.continuous_mul_log.intervalIntegrable 0 t)
  simpa [F, pow_two, mul_assoc] using h

theorem integral_radius_log_max {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..1, r * Real.log (max r t)) = unitDiskLogProfile t / 2 := by
  by_cases ht0 : t = 0
  · subst t
    have he : (∫ r in (0 : ℝ)..1, r * Real.log (max r 0)) =
        ∫ r in (0 : ℝ)..1, r * Real.log r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by simpa using hr.1
      change r * Real.log (max r 0) = r * Real.log r
      rw [max_eq_left hr0]
    rw [he, integral_radius_mul_log (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num [unitDiskLogProfile]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hc : Continuous (fun r : ℝ => r * Real.log (max r t)) := by
    exact continuous_id.mul ((continuous_id.max continuous_const).log
      (fun r => ne_of_gt (htpos.trans_le (le_max_right r t))))
  by_cases ht1 : t ≤ 1
  · have hlo : (∫ r in (0 : ℝ)..t, r * Real.log (max r t)) =
        t ^ 2 * Real.log t / 2 := by
      calc
        _ = ∫ r in (0 : ℝ)..t, r * Real.log t := by
          apply intervalIntegral.integral_congr
          intro r hr
          change r * Real.log (max r t) = r * Real.log t
          rw [uIcc_of_le ht] at hr
          rw [max_eq_right hr.2]
        _ = _ := by rw [intervalIntegral.integral_mul_const, integral_id]; ring
    have hhi : (∫ r in t..1, r * Real.log (max r t)) =
        -1 / 4 - (t ^ 2 * Real.log t / 2 - t ^ 2 / 4) := by
      have he : (∫ r in t..1, r * Real.log (max r t)) =
          ∫ r in t..1, r * Real.log r := by
        apply intervalIntegral.integral_congr
        intro r hr
        change r * Real.log (max r t) = r * Real.log r
        rw [uIcc_of_le ht1] at hr
        rw [max_eq_left hr.1]
      have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_mul_log.intervalIntegrable 0 t)
        (Real.continuous_mul_log.intervalIntegrable t 1)
      rw [integral_radius_mul_log (by norm_num : (0 : ℝ) ≤ 1), integral_radius_mul_log ht] at hs
      rw [he]
      norm_num at hs
      linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 1)
    rw [hlo, hhi] at hsplit
    rw [← hsplit, unitDiskLogProfile, if_pos ht1]
    ring
  · have hge : 1 ≤ t := (lt_of_not_ge ht1).le
    calc
      _ = ∫ r in (0 : ℝ)..1, r * Real.log t := by
        apply intervalIntegral.integral_congr
        intro r hr
        change r * Real.log (max r t) = r * Real.log t
        rw [max_eq_right ((by simpa using hr.2 : r ≤ 1).trans hge)]
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, integral_id, unitDiskLogProfile, if_neg ht1]
        ring

theorem unitDiskLogProfile_lower {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) - (Real.log 2 + 1 / 2) ≤ unitDiskLogProfile t := by
  unfold unitDiskLogProfile
  split_ifs with h
  · have hl := Real.log_le_log (by positivity : 0 < 1 + t) (by linarith : 1 + t ≤ 2)
    nlinarith [sq_nonneg t]
  · have ht1 : 1 ≤ t := (lt_of_not_ge h).le
    have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hl := Real.log_le_log (by positivity : 0 < 1 + t) (by linarith : 1 + t ≤ 2 * t)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) htp.ne'] at hl
    linarith

end RepulsiveCoulomb
