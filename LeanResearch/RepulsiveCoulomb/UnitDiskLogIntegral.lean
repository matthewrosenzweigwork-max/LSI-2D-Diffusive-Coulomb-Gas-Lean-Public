module

public import LeanResearch.RepulsiveCoulomb.UnitDiskLogRadial

@[expose] public section

/-! Literal Lebesgue disk average, including integrability of the logarithmic
singularity and the radial Jacobian. All equalities concern the original log. -/
noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem log_distance_unitDisk_integrable (y : ℂ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z - y‖) (closedBall (0 : ℂ) 1) := by
  have hp := (equilibriumLogPositive_integrable.comp_sub_right y).integrableOn
    (s := closedBall (0 : ℂ) 1)
  have hm : IntegrableOn equilibriumLogMoment (closedBall (0 : ℂ) 1) :=
    equilibriumLogMoment_continuous.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)
  have hc : IntegrableOn (fun _ : ℂ => equilibriumLogMoment y) (closedBall (0 : ℂ) 1) :=
    integrableOn_const (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  apply ((hp.add hm).add hc).mono'
    ((Real.measurable_log.comp (continuous_id.sub continuous_const).norm.measurable).aestronglyMeasurable)
  exact Eventually.of_forall (fun z => by
    have h := equilibriumLogKernel_abs_sub_bound z y
    simpa only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, id_eq,
      equilibriumLogKernel, abs_neg, Real.norm_eq_abs] using h)

theorem complex_integrable_polar {f : ℂ → ℝ} (hm : Measurable f) (hi : Integrable f) :
    Integrable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)) :=
    measurable_fst.mul (hm.comp continuous_complex_polarCoord_symm.measurable)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hfinite := (hasFiniteIntegral_iff_norm f).mp hi.hasFiniteIntegral
  have hp := Complex.lintegral_comp_polarCoord_symm (fun z => ENNReal.ofReal ‖f z‖)
  rw [← hp] at hfinite
  rw [Measure.prod_restrict]
  change (∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal ‖p.1 * f (Complex.polarCoord.symm p)‖) < ⊤
  convert hfinite using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  change ENNReal.ofReal ‖p.1 * f (Complex.polarCoord.symm p)‖ =
    ENNReal.ofReal p.1 * ENNReal.ofReal ‖f (Complex.polarCoord.symm p)‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hp.1, ENNReal.ofReal_mul hp.1.le]

theorem complex_integral_polar {f : ℂ → ℝ} (hm : Measurable f) (hi : Integrable f) :
    (∫ z : ℂ, f z) = ∫ R in Ioi (0 : ℝ), R *
      ∫ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) := by
  rw [← Complex.integral_comp_polarCoord_symm]
  change (∫ p : ℝ × ℝ, p.1 * f (Complex.polarCoord.symm p)
    ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [← Measure.prod_restrict, integral_prod _ (complex_integrable_polar hm hi)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun R => integral_const_mul R _)

theorem unitDisk_integral_polar {f : ℂ → ℝ} (hm : Measurable f)
    (hi : IntegrableOn f (closedBall (0 : ℂ) 1)) :
    (∫ z in closedBall (0 : ℂ) 1, f z) =
      (2 * Real.pi) * ∫ R in (0 : ℝ)..1, R * Real.circleAverage f 0 R := by
  let g := (closedBall (0 : ℂ) 1).indicator f
  have hgm : Measurable g := hm.indicator isClosed_closedBall.measurableSet
  have hgi : Integrable g := (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr hi
  rw [← integral_indicator isClosed_closedBall.measurableSet, complex_integral_polar hgm hgi]
  have he : (fun R : ℝ => R * ∫ θ in Ioo (-Real.pi) Real.pi,
      g (Complex.polarCoord.symm (R, θ))) =ᵐ[volume.restrict (Ioi 0)]
      (Ioc (0 : ℝ) 1).indicator (fun R => R * ∫ θ in Ioo (-Real.pi) Real.pi,
        f (Complex.polarCoord.symm (R, θ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    have hn (θ : ℝ) : ‖Complex.polarCoord.symm (R, θ)‖ = R := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hR]
    by_cases hR1 : R ≤ 1
    · have hz (θ : ℝ) : Complex.polarCoord.symm (R, θ) ∈ closedBall (0 : ℂ) 1 := by
        simpa only [mem_closedBall, dist_zero_right, hn] using hR1
      simp only [g, Set.indicator_of_mem (show R ∈ Ioc (0 : ℝ) 1 from ⟨hR, hR1⟩)]
      simp_rw [Set.indicator_of_mem (hz _)]
    · have hz (θ : ℝ) : Complex.polarCoord.symm (R, θ) ∉ closedBall (0 : ℂ) 1 := by
        simpa only [mem_closedBall, dist_zero_right, hn] using hR1
      simp only [g, Set.indicator_of_notMem (show R ∉ Ioc (0 : ℝ) 1 from fun h => hR1 h.2)]
      simp_rw [Set.indicator_of_notMem (hz _)]
      simp
  rw [integral_congr_ae he, setIntegral_indicator measurableSet_Ioc]
  have hs : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := inter_eq_right.mpr (fun _ h => h.1)
  rw [hs]
  have hang (R : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi,
      f (Complex.polarCoord.symm (R, θ))) = (2 * Real.pi) * Real.circleAverage f 0 R := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact angularIntegral_eq_circleAverage f R
  simp_rw [hang]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro R _
  ring

theorem unitDisk_log_integral (y : ℂ) :
    (∫ z in closedBall (0 : ℂ) 1, Real.log ‖z - y‖) =
      Real.pi * unitDiskLogProfile ‖y‖ := by
  rw [unitDisk_integral_polar (f := fun z : ℂ => Real.log ‖z - y‖)
    (Real.measurable_log.comp (continuous_id.sub continuous_const).norm.measurable)
    (log_distance_unitDisk_integrable y)]
  have he : (∫ R in (0 : ℝ)..1, R * Real.circleAverage (fun z : ℂ => Real.log ‖z - y‖) 0 R) =
      ∫ R in (0 : ℝ)..1, R * Real.log (max R ‖y‖) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro R hR
    change R * Real.circleAverage (fun z : ℂ => Real.log ‖z - y‖) 0 R =
      R * Real.log (max R ‖y‖)
    have hc := equilibriumCircularKernel_eq_circleAverage hR.1 (0 : ℂ) y
    have hn : Real.circleAverage (fun z : ℂ => equilibriumLogKernel (z - y)) 0 R =
        -Real.circleAverage (fun z : ℂ => Real.log ‖z - y‖) 0 R := by
      simpa only [equilibriumLogKernel, smul_eq_mul, neg_one_mul] using
        (Real.circleAverage_fun_smul (a := (-1 : ℝ))
          (f := fun z : ℂ => Real.log ‖z - y‖) (c := 0) (R := R))
    rw [hn] at hc
    simp only [equilibriumCircularKernel, zero_sub, norm_neg] at hc
    have heq := neg_injective hc
    rw [heq]
  rw [he, integral_radius_log_max (norm_nonneg y)]
  ring

theorem unitDisk_log_average (y : ℂ) :
    (⨍ z in closedBall (0 : ℂ) 1, Real.log ‖z - y‖) =
      if ‖y‖ ≤ 1 then (‖y‖ ^ 2 - 1) / 2 else Real.log ‖y‖ := by
  rw [average_eq, unitDisk_log_integral]
  have hv : (volume.restrict (closedBall (0 : ℂ) 1)).real univ = Real.pi := by
    simp [Measure.real, Complex.volume_closedBall]
  rw [hv]
  change Real.pi⁻¹ * (Real.pi * unitDiskLogProfile ‖y‖) = _
  rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  rfl

theorem unitDisk_log_average_lower (y : ℂ) :
    Real.log (1 + ‖y‖) - (Real.log 2 + 1 / 2) ≤
      ⨍ z in closedBall (0 : ℂ) 1, Real.log ‖z - y‖ := by
  rw [unitDisk_log_average]
  exact unitDiskLogProfile_lower (norm_nonneg y)

end RepulsiveCoulomb
