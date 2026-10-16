module

public import LeanResearch.RepulsiveCoulomb.PointConformalCumulativeVariation
public import LeanResearch.RepulsiveCoulomb.PointConformalMetricSpeedLower
public import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzMetric

@[expose] public section

/-! The physical weighted derivative integral equals actual conformal partition
variation for every Euclidean Lipschitz curve.  The reverse inequality is proved
by the scalar absolutely-continuous cumulative variation and genuine local
analytic metric charts, with the vanishing density handled at punctures. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem pointConformalLipschitz_physical_le_metricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    pointConformalPathELength a y γ s t ≤ pointConformalMetricLength ha y γ s t := by
  by_cases hst : s ≤ t
  swap
  · simp only [pointConformalPathELength, Icc_eq_empty_of_lt (lt_of_not_ge hst),
      Measure.restrict_empty, lintegral_zero_measure, zero_le]
  obtain ⟨L, f, hf, hm, hfs, hft, hdom⟩ := exists_pointConformal_lipschitz_cumulative ha y hγ hst
  have hac : AbsolutelyContinuousOnInterval f s t := by
    rw [← uIcc_of_le hst] at hf
    exact hf.absolutelyContinuousOnInterval
  have hfdiff : ∀ᵐ u ∂volume.restrict (Icc s t), DifferentiableAt ℝ f u := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    simpa only [uIcc_of_le hst] using hac.ae_differentiableAt
  have hinterior : ∀ᵐ u ∂volume.restrict (Icc s t), u ∈ Ioo s t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact self_mem_ae_restrict measurableSet_Ioo
  have hnonneg : ∀ᵐ u ∂volume.restrict (Icc s t), 0 ≤ deriv f u := by
    filter_upwards [hinterior] with u hu
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
    exact hm.derivWithin_nonneg
  have hspeed : ∀ᵐ u ∂volume.restrict (Icc s t),
      pointConformalDensity a y (γ u) * ‖deriv γ u‖ ≤ deriv f u := by
    filter_upwards [lipschitzOn_Icc_ae_differentiableAt_complex hγ, hfdiff,
      hinterior, hnonneg] with u huγ huf hu hnn
    have hlocal : ∀ᶠ v in 𝓝 u,
        (pointSmoothConformalEDist a y (γ v) (γ u)).toReal ≤ dist (f v) (f u) := by
      filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv
      exact hdom v hv u ⟨hu.1.le, hu.2.le⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using
      pointConformal_physical_speed_le_norm_deriv ha y huγ huf hlocal
  have hint : IntegrableOn (deriv f) (Icc s t) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst).1 hac.intervalIntegrable_deriv
  have hFTC : (∫ u in Icc s t, deriv f u) = (pointConformalMetricLength ha y γ s t).toReal := by
    have h := hac.integral_deriv_eq_sub
    rw [intervalIntegral.integral_of_le hst, restrict_Ioc_eq_restrict_Icc, hft, hfs, sub_zero] at h
    exact h
  calc
    pointConformalPathELength a y γ s t ≤ ∫⁻ u in Icc s t, ENNReal.ofReal (deriv f u) := by
      unfold pointConformalPathELength
      apply lintegral_mono_ae
      filter_upwards [hspeed] with u hu
      rw [← ENNReal.ofReal_mul (pointConformalDensity_nonneg a y _)]
      exact ENNReal.ofReal_le_ofReal hu
    _ = ENNReal.ofReal (∫ u in Icc s t, deriv f u) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = pointConformalMetricLength ha y γ s t := by
      rw [hFTC, ENNReal.ofReal_toReal (pointConformalLipschitz_metricLength_ne_top ha y hγ)]

theorem pointConformalLipschitz_physical_eq_metricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    pointConformalPathELength a y γ s t = pointConformalMetricLength ha y γ s t :=
  le_antisymm (pointConformalLipschitz_physical_le_metricLength ha y hγ)
    (pointConformalMetricLength_le_lipschitz_physical ha y hγ)

end RepulsiveCoulomb
