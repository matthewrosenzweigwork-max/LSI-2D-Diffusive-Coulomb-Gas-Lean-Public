import LeanResearch.RepulsiveCoulomb.MetricCumulativeVariation
import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzLength
import LeanResearch.RepulsiveCoulomb.PointConformalIntrinsicLength

/-! Actual scalar cumulative variation for the finite-point conformal metric.
Every Euclidean Lipschitz curve is also Lipschitz in this metric on its compact
parameter interval; no inverse Lipschitz estimate is assumed at punctures. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConformalLipschitz_metric_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    ∃ L : NNReal, ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
      (pointSmoothConformalEDist a y (γ u) (γ v)).toReal ≤ (L : ℝ) * dist u v := by
  have hcompact := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  let B : NNReal := ⟨Real.sqrt (rawPointBallFactor a y 0 (3 * R)), Real.sqrt_nonneg _⟩
  refine ⟨B * K, ?_⟩
  intro u hu v hv
  have huR : ‖γ u‖ ≤ R := hR (γ u) ⟨u, hu, rfl⟩
  have hvR : ‖γ v‖ ≤ R := hR (γ v) ⟨v, hv, rfl⟩
  have hcoef := Real.sqrt_le_sqrt (rawPointBallFactor_segment_le_bounded ha y huR hvR)
  calc
    _ ≤ Real.sqrt (rawPointBallFactor a y (γ u) ‖γ v - γ u‖) * ‖γ v - γ u‖ :=
      pointConformalDistance_segment_upper ha y (γ u) (γ v)
    _ ≤ (B : ℝ) * ‖γ v - γ u‖ :=
      mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = (B : ℝ) * dist (γ u) (γ v) := by rw [dist_eq_norm']
    _ ≤ (B : ℝ) * ((K : ℝ) * dist u v) :=
      mul_le_mul_of_nonneg_left (hγ.dist_le_mul u hu v hv) B.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul, mul_assoc]

theorem exists_pointConformal_lipschitz_cumulative {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) (hst : s ≤ t) :
    ∃ L : NNReal, ∃ f : ℝ → ℝ,
      LipschitzOnWith L f (Icc s t) ∧ MonotoneOn f (Icc s t) ∧ f s = 0 ∧
      f t = (pointConformalMetricLength ha y γ s t).toReal ∧
      ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
        (pointSmoothConformalEDist a y (γ u) (γ v)).toReal ≤ dist (f u) (f v) := by
  obtain ⟨L, hL⟩ := pointConformalLipschitz_metric_bound ha y hγ
  have hγ' := (@lipschitzOnWith_iff_dist_le_mul ℝ ℂ inferInstance
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace L (Icc s t) γ).2 hL
  obtain ⟨f, hf, hm, hs, ht, hd⟩ := @exists_lipschitz_metric_cumulative ℂ
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ s t L hγ' hst
  exact ⟨L, f, hf, hm, hs, ht, hd⟩

theorem pointConformalLipschitz_metricLength_ne_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    pointConformalMetricLength ha y γ s t ≠ ⊤ := by
  obtain ⟨L, hL⟩ := pointConformalLipschitz_metric_bound ha y hγ
  have hγ' := (@lipschitzOnWith_iff_dist_le_mul ℝ ℂ inferInstance
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace L (Icc s t) γ).2 hL
  exact @lipschitz_boundedVariationOn_Icc ℂ
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ s t L hγ' 

end RepulsiveCoulomb
