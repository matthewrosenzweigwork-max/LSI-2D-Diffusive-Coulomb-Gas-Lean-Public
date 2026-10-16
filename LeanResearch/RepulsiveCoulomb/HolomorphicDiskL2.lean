import LeanResearch.RepulsiveCoulomb.HolomorphicCircleL2
import LeanResearch.RepulsiveCoulomb.RawPointWeightGeometry

/-! A disk L2 point-evaluation bound, proved by a positive-width polar annulus. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem holomorphic_disk_two_lintegral_lower {f : ℂ → ℂ} (hc : Continuous f)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 2)) :
    ENNReal.ofReal ((2 * Real.pi) * ‖f 0‖ ^ 2) ≤
      ∫⁻ z in closedBall (0 : ℂ) 2, ENNReal.ofReal (‖f z‖ ^ 2) := by
  let g : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) 2).indicator (fun z => ENNReal.ofReal (‖f z‖ ^ 2))
  have hg : Measurable g := (hc.norm.pow 2).measurable.ennreal_ofReal.indicator isClosed_closedBall.measurableSet
  have hpoint : ∀ᵐ R ∂volume.restrict (Ioc (1 : ℝ) 2),
      ENNReal.ofReal ((2 * Real.pi) * ‖f 0‖ ^ 2) ≤
        ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (Complex.polarCoord.symm (R, θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
    have hr : 0 < R := lt_trans zero_lt_one hR.1
    have hav : ‖f 0‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 R :=
      holomorphic_circle_norm_sq_lower hr ⟨hf.mono (ball_subset_ball hR.2), hc.continuousOn⟩
    have ha : ENNReal.ofReal ((2 * Real.pi) * ‖f 0‖ ^ 2) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖f (Complex.polarCoord.symm (R, θ))‖ ^ 2) := by
      rw [angularLIntegral_eq_circleAverage (fun z => ‖f z‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _) R]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hav Real.two_pi_pos.le)
    have he : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖f (Complex.polarCoord.symm (R, θ))‖ ^ 2)) =
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (Complex.polarCoord.symm (R, θ)) := by
      apply lintegral_congr
      intro θ
      have hn : ‖Complex.polarCoord.symm (R, θ)‖ = R := by
        rw [polarCoord_symm_eq_circleMap, norm_circleMap_zero, abs_of_pos hr]
      have hz : Complex.polarCoord.symm (R, θ) ∈ closedBall (0 : ℂ) 2 := by
        simpa only [mem_closedBall, dist_zero_right, hn] using hR.2
      simp only [g, Set.indicator_of_mem hz]
    rw [he] at ha
    have hr' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal R := by
      simpa using ENNReal.ofReal_le_ofReal hR.1.le
    apply ha.trans
    calc
      _ = 1 * (∫⁻ θ in Ioo (-Real.pi) Real.pi, g (Complex.polarCoord.symm (R, θ))) := (one_mul _).symm
      _ ≤ _ := by gcongr

  calc
    _ = ∫⁻ R in Ioc (1 : ℝ) 2, ENNReal.ofReal ((2 * Real.pi) * ‖f 0‖ ^ 2) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      norm_num
    _ ≤ ∫⁻ R in Ioc (1 : ℝ) 2, ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (Complex.polarCoord.symm (R, θ)) := lintegral_mono_ae hpoint
    _ ≤ ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (Complex.polarCoord.symm (R, θ)) :=
      lintegral_mono_set (fun R hR => lt_trans zero_lt_one hR.1)
    _ = ∫⁻ z, g z := (complex_lintegral_polar g hg).symm
    _ = _ := lintegral_indicator isClosed_closedBall.measurableSet _

theorem holomorphic_disk_two_integral_lower {f : ℂ → ℂ} (hc : Continuous f)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 2)) :
    (2 * Real.pi) * ‖f 0‖ ^ 2 ≤ ∫ z in closedBall (0 : ℂ) 2, ‖f z‖ ^ 2 := by
  have h := holomorphic_disk_two_lintegral_lower hc hf
  have hi : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2) (closedBall (0 : ℂ) 2) volume :=
    (hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp h

end RepulsiveCoulomb
