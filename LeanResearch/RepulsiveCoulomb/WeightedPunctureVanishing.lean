import LeanResearch.RepulsiveCoulomb.WeightedPunctureMassBound
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Vanishing weighted local mass gives the sharp endpoint little-o control at a puncture. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem shrinking_complex_ball_volume :
    Tendsto (fun c : ℂ => volume (ball (0 : ℂ) (2 * ‖c‖))) (𝓝 0) (𝓝 0) := by
  have hr : Tendsto (fun c : ℂ => ENNReal.ofReal (2 * ‖c‖)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun c : ℂ => (2 : ℝ) * ‖c‖) := continuous_const.mul continuous_norm
    simpa only [norm_zero, mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hc.tendsto (0 : ℂ))
  have hs := ENNReal.Tendsto.mul_const ((ENNReal.continuous_pow 2).tendsto 0 |>.comp hr) (b := (NNReal.pi : ℝ≥0∞)) (by simp)
  simpa only [Function.comp_apply, Complex.volume_ball, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using hs

theorem local_integral_shrinking_complex_ball {g : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hg : IntegrableOn g (ball (0 : ℂ) R)) :
    Tendsto (fun c : ℂ => ∫ z in ball (0 : ℂ) (2 * ‖c‖), g z) (𝓝 0) (𝓝 0) := by
  have hv : Tendsto (fun c : ℂ => (volume.restrict (ball (0 : ℂ) R)) (ball (0 : ℂ) (2 * ‖c‖)))
      (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds shrinking_complex_ball_volume
      (fun _ => zero_le) (fun _ => Measure.restrict_apply_le _ _)
  have h := hg.tendsto_setIntegral_nhds_zero hv
  apply h.congr'
  filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < R / 2)] with c hc
  have hc' : ‖c‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hc
  have hs : ball (0 : ℂ) (2 * ‖c‖) ⊆ ball (0 : ℂ) R := ball_subset_ball (by linarith)
  rw [Measure.restrict_restrict_of_subset hs]

theorem weighted_holomorphic_square_pole_tendsto {f : ℂ → ℂ} {a R : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}))
    (hi : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (ball (0 : ℂ) R)) :
    Tendsto (fun z : ℂ => z ^ 2 * f z) (𝓝 0) (𝓝 0) := by
  have hm := local_integral_shrinking_complex_ball hR hi
  have hu : ∀ᶠ c : ℂ in 𝓝 0, (Real.pi / 32) * ‖c ^ 2 * f c‖ ^ 2 ≤
      4 * ∫ z in ball (0 : ℂ) (2 * ‖c‖), ‖z‖ ^ a * ‖f z‖ ^ 2 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < R / 2),
      ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with c hc hr
    have hc' : ‖c‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hc
    have hr' : ‖c‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hr : ‖c‖ < 1).le
    by_cases hz : c = 0
    · subst c
      simp
    · exact weighted_holomorphic_square_pole_bound ha ha2 hf hi hz hr' hc'
  have hq : Tendsto (fun c : ℂ => (Real.pi / 32) * ‖c ^ 2 * f c‖ ^ 2) (𝓝 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) hu
      (by simpa using hm.const_mul (4 : ℝ))
  have hs : Tendsto (fun c : ℂ => ‖c ^ 2 * f c‖ ^ 2) (𝓝 0) (𝓝 0) := by
    convert hq.div_const (Real.pi / 32) using 1
    · funext c
      field_simp
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

end RepulsiveCoulomb
