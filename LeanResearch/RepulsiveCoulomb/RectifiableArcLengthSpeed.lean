import LeanResearch.RepulsiveCoulomb.RectifiableArcLengthParameter
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! The constructed Euclidean arclength parameter has unit speed almost
everywhere. This makes integration in its parameter the literal Euclidean ds
integral, including curves with an originally singular BV parametrization. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem pointConformalMetricLength_zero_weight (γ : ℝ → ℂ) (s t : ℝ) :
    pointConformalMetricLength
      (a := standardConeExponents 0) (by intro j; simp [standardConeExponents])
      standardConeLocations γ s t = eVariationOn γ (Icc s t) := by
  unfold pointConformalMetricLength eVariationOn
  apply iSup_congr
  rintro ⟨n, u, hu, hmem⟩
  apply Finset.sum_congr rfl
  intro i hi
  change pointSmoothConformalEDist (standardConeExponents 0) standardConeLocations
    (γ (u (i + 1))) (γ (u i)) = edist (γ (u (i + 1))) (γ (u i))
  rw [standardCone_zero_distance, edist_dist, dist_eq_norm, norm_sub_rev]

theorem complex_lipschitz_eVariation_le_deriv_integral {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    eVariationOn γ (Icc s t) ≤ ∫⁻ u in Icc s t, ENNReal.ofReal ‖deriv γ u‖ := by
  have h := pointConformalMetricLength_le_lipschitz_physical
    (a := standardConeExponents 0) (by intro j; simp [standardConeExponents])
    standardConeLocations hγ
  rw [pointConformalMetricLength_zero_weight] at h
  simpa only [pointConformalPathELength, standardCone_density, Real.rpow_zero,
    ENNReal.ofReal_one, one_mul] using h

theorem lipschitzOn_one_deriv_norm_le_ae {η : ℝ → ℂ} {L : ℝ}
    (hη : LipschitzOnWith 1 η (Icc 0 L)) :
    ∀ᵐ u ∂volume.restrict (Icc 0 L), ‖deriv η u‖ ≤ 1 := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hu.1 hu.2) hη

/-- A 1-Lipschitz curve whose total variation equals its parameter interval
has speed exactly one almost everywhere, without a differentiability premise. -/
theorem arcLength_unit_speed_ae {η : ℝ → ℂ} {L : ℝ}
    (hη : LipschitzOnWith 1 η (Icc 0 L))
    (hvar : eVariationOn η (Icc 0 L) = ENNReal.ofReal L) :
    ∀ᵐ u ∂volume.restrict (Icc 0 L), ‖deriv η u‖ = 1 := by
  have hle : (fun u ↦ ENNReal.ofReal ‖deriv η u‖) ≤ᵐ[volume.restrict (Icc 0 L)]
      (fun _ ↦ (1 : ℝ≥0∞)) := by
    filter_upwards [lipschitzOn_one_deriv_norm_le_ae hη] with u hu
    exact (ENNReal.ofReal_le_ofReal hu).trans_eq ENNReal.ofReal_one
  have hconst : (∫⁻ _u : ℝ in Icc 0 L, (1 : ℝ≥0∞)) = ENNReal.ofReal L := by simp
  have hlower := complex_lipschitz_eVariation_le_deriv_integral hη
  rw [hvar] at hlower
  have hupper := lintegral_mono_ae hle
  rw [hconst] at hupper
  have hae := ae_eq_of_ae_le_of_lintegral_le hle
    (ne_of_lt (hupper.trans_lt ENNReal.ofReal_lt_top))
    aemeasurable_const (by rw [hconst]; exact hlower)
  filter_upwards [hae] with u hu
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_one] using
    congrArg ENNReal.toReal hu

/-- All continuous rectifiable planar curves admit a true unit-speed arclength
factorization, including constant curves (whose parameter interval has measure zero). -/
theorem exists_rectifiable_unitSpeed_factor {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    ∃ η : ℝ → ℂ,
      LipschitzOnWith 1 η (Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal) ∧
      η 0 = γ 0 ∧ η (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = γ 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η (rectifiableCumulativeLength γ t) = γ t) ∧
      η '' Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = γ '' Icc (0 : ℝ) 1 ∧
      eVariationOn η (Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal) =
        eVariationOn γ (Icc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal), ‖deriv η u‖ = 1 := by
  obtain ⟨η, hη, h0, h1, hfactor, himage, hvar⟩ := exists_rectifiable_arcLength_factor hb hc
  refine ⟨η, hη, h0, h1, hfactor, himage, hvar, arcLength_unit_speed_ae hη ?_⟩
  rw [hvar, ENNReal.ofReal_toReal hb]

end RepulsiveCoulomb
