module

public import LeanResearch.RepulsiveCoulomb.PointConformalLocalMetric

@[expose] public section

/-! Actual ambient metric charts for the literal point-density metric. The singular
model is the previously constructed singleton smooth-path metric. Its identification
with the classical quotient Euclidean cone remains a separate obligation. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace RepulsiveCoulomb

theorem exists_pointConformal_flat_metric_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r,
        pointSmoothConformalEDist a y u v = ENNReal.ofReal ‖e v - e u‖ := by
  obtain ⟨e, hep, he0, _, hinv, he⟩ := exists_pointConformal_flat_chart_with_inverse ha y hp
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents 0) standardConeLocations (e z) * ‖deriv e z‖ =
        pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density, Real.rpow_zero, one_mul]
    exact (he z hz).2.1
  have hb : ∀ j, 0 ≤ standardConeExponents 0 j := by simp [standardConeExponents]
  obtain ⟨r, hr, hsub, hmetric⟩ := pointConformal_chart_local_metric_eq ha y hb standardConeLocations e hF hinv hep
  refine ⟨e, r, hr, he0, hsub, ?_⟩
  intro u hu v hv
  rw [hmetric u hu v hv, standardCone_zero_distance]

theorem exists_pointConformal_cone_metric_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r,
        pointSmoothConformalEDist a y u v =
          pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
            standardConeLocations (e u) (e v) := by
  obtain ⟨e, hep, he0, hinv, he⟩ := exists_pointConformal_cone_chart_with_inverse ha y p
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents (coalescedPointExponent a y p / 2))
        standardConeLocations (e z) * ‖deriv e z‖ = pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density]
    exact (he z hz).2.2
  have hb : ∀ j, 0 ≤ standardConeExponents (coalescedPointExponent a y p / 2) j := by
    intro j
    exact mul_nonneg (by norm_num) (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
  obtain ⟨r, hr, hsub, hmetric⟩ := pointConformal_chart_local_metric_eq ha y hb standardConeLocations e hF hinv hep
  exact ⟨e, r, hr, he0, hsub, hmetric⟩

end RepulsiveCoulomb
