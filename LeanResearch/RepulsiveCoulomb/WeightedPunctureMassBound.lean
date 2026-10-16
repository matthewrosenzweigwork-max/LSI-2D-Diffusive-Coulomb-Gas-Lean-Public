import LeanResearch.RepulsiveCoulomb.PuncturedDiskGeometry

/-! The local weighted L2 estimate retaining vanishing mass at the endpoint exponent two. -/
noncomputable section
open Set MeasureTheory Metric Filter
namespace RepulsiveCoulomb

theorem puncture_weighted_integral_comparison {f : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a) (c : ℂ)
    (h1 : IntegrableOn (fun z => ‖f z‖ ^ 2) (closedBall c (‖c‖ / 4)))
    (h2 : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (closedBall c (‖c‖ / 4))) :
    ‖c‖ ^ a * (∫ z in closedBall c (‖c‖ / 4), ‖f z‖ ^ 2) ≤
      (2 : ℝ) ^ a * ∫ z in closedBall c (‖c‖ / 4), ‖z‖ ^ a * ‖f z‖ ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono_ae (h1.const_mul _) (h2.const_mul _)
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
  have hp := Real.rpow_le_rpow (norm_nonneg c) (puncture_local_norm_lower hz) ha
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)] at hp
  calc
    _ ≤ ((2 : ℝ) ^ a * ‖z‖ ^ a) * ‖f z‖ ^ 2 := mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = _ := by ring

theorem weighted_holomorphic_square_pole_bound {f : ℂ → ℂ} {a R : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}))
    (hi : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (ball (0 : ℂ) R))
    {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) (hR : ‖c‖ < R / 2) :
    (Real.pi / 32) * ‖c ^ 2 * f c‖ ^ 2 ≤
      4 * ∫ z in ball (0 : ℂ) (2 * ‖c‖), ‖z‖ ^ a * ‖f z‖ ^ 2 := by
  have hp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 < ‖c‖ / 8 := by positivity
  have hd : DifferentiableOn ℂ f (ball c (4 * (‖c‖ / 8))) := by
    convert hf.mono (punctured_centered_ball_subset hc hR) using 1 <;> congr 1 <;> ring
  have hloc := holomorphic_local_disk_integral_lower c hr hd
  have hrad : 2 * (‖c‖ / 8) = ‖c‖ / 4 := by ring
  rw [hrad] at hloc
  have hsub := puncture_local_closedBall_avoids hc hR
  have hnorm : IntegrableOn (fun z => ‖f z‖ ^ 2) (closedBall c (‖c‖ / 4)) :=
    ((hf.continuousOn.mono hsub).norm.pow 2).integrableOn_compact (isCompact_closedBall c (‖c‖ / 4))
  have hw := hi.mono_set (fun z hz => (hsub hz).1)
  have hm := hi.mono_set (ball_subset_ball (by linarith : 2 * ‖c‖ ≤ R))
  have hmass : (∫ z in closedBall c (‖c‖ / 4), ‖z‖ ^ a * ‖f z‖ ^ 2) ≤
      ∫ z in ball (0 : ℂ) (2 * ‖c‖), ‖z‖ ^ a * ‖f z‖ ^ 2 :=
    setIntegral_mono_set hm (Eventually.of_forall (fun z =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg z) a) (sq_nonneg _)))
      (Eventually.of_forall (fun z hz => puncture_local_closedBall_subset hc hz))
  have hcomp := puncture_weighted_integral_comparison ha c hnorm hw
  have h2 : (2 : ℝ) ^ a ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2
    norm_num only [Real.rpow_two] at h
    exact h
  have hmass0 : 0 ≤ ∫ z in ball (0 : ℂ) (2 * ‖c‖), ‖z‖ ^ a * ‖f z‖ ^ 2 :=
    integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z) a) (sq_nonneg _))
  have hb : ‖c‖ ^ a * ((2 * Real.pi) * (‖c‖ / 8) ^ 2 * ‖f c‖ ^ 2) ≤
      4 * ∫ z in ball (0 : ℂ) (2 * ‖c‖), ‖z‖ ^ a * ‖f z‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hloc (Real.rpow_nonneg (norm_nonneg c) a)).trans
      (hcomp.trans ((mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg (by norm_num) a)).trans
        (mul_le_mul_of_nonneg_right h2 hmass0)))
  have ht : ‖c‖ ^ 2 ≤ ‖c‖ ^ a := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hp hc1 ha2
  calc
    _ = ((Real.pi / 32) * ‖c‖ ^ 2 * ‖f c‖ ^ 2) * ‖c‖ ^ 2 := by
      rw [norm_mul, norm_pow, mul_pow]
      ring
    _ ≤ ((Real.pi / 32) * ‖c‖ ^ 2 * ‖f c‖ ^ 2) * ‖c‖ ^ a :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = ‖c‖ ^ a * ((2 * Real.pi) * (‖c‖ / 8) ^ 2 * ‖f c‖ ^ 2) := by ring
    _ ≤ _ := hb

end RepulsiveCoulomb
