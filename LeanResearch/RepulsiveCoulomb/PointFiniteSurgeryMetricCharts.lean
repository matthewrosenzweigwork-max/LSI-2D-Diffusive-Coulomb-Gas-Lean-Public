module

public import LeanResearch.RepulsiveCoulomb.PointLocalChartMetricShrink
public import LeanResearch.RepulsiveCoulomb.PointFiniteSurgeryAllPointCharts

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual sharp local metric charts at every point,
constructed from the original coefficients. The finite branch estimates are
globalized before a source restriction. No complete surgery metric or rigid
overlap is assumed or concluded here. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

namespace PointFiniteSurgeryLocalModel
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

theorem global_lower_bound (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (x z : ℂ) (hx : x ∈ D.chart.source) (hz : z ∈ D.chart.source) :
    c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (D.chart x) (D.chart z) := by
  cases D with
  | sectorInterior i hopen hp =>
      exact (pointActualSectorInteriorOpenChart_dist_bounds ha (L.get i) hc hc1 hopen x z hx hz).1
  | unchanged data =>
      change c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (data.chart x) (data.chart z)
      rw [data.metric x z hx hz]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg hc1
  | incident data => exact data.global_lower_bound x z hx hz

theorem centered_forward_bound (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (x : ℂ) (hx : x ∈ D.chart.source) :
    ∀ᶠ z in 𝓝 x, dist (D.chart x) (D.chart z) ≤ (pointSmoothConformalEDist a y x z).toReal := by
  cases D with
  | sectorInterior i hopen hp =>
      filter_upwards [hopen.mem_nhds hx] with z hz
      exact (pointActualSectorInteriorOpenChart_dist_bounds ha (L.get i) hc hc1 hopen x z hx hz).2
  | unchanged data =>
      filter_upwards [data.chart.open_source.mem_nhds hx] with z hz
      exact (data.metric x z hx hz).le
  | incident data => exact data.centered_forward_bound x hx

/-- The actual chart function is retained, so all occupied/complement
formulas and eventual overlap identities survive this restriction. -/
theorem exists_metric_shrink (D : PointFiniteSurgeryLocalModel ha L p c hc hc1) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      p ∈ e.source ∧ e.source ⊆ D.chart.source ∧ (e : ℂ → ℂ) = D.chart ∧
      ∀ x ∈ e.source, ∀ z ∈ e.source,
        c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (e x) (e z) ∧
          dist (e x) (e z) ≤ (pointSmoothConformalEDist a y x z).toReal :=
  exists_pointConformal_chart_metric_shrink ha y D.chart p D.center_mem
    (fun x hx z hz ↦ D.global_lower_bound x z hx hz) D.centered_forward_bound

end PointFiniteSurgeryLocalModel

/-- Original-input metric-chart endpoint. All maps are actual local surgery
charts with sharp c/1 source-pair bounds. It deliberately retains the actual
unshrunk models so that rigid overlap construction can use their provenance. -/
theorem point_original_plane_finite_surgery_metric_charts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ c : ℝ, ∃ L : List (PointActualAllocatedSector a y),
      c = 1 / (1 + pointExteriorHalfMass a) ∧
      ∃ hc : 0 < c, ∃ hc1 : c ≤ 1,
      L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      (∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
        z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0) ∧
      (∀ p, (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p) ∧
      ∃ model : ∀ p : ℂ, PointFiniteSurgeryLocalModel ha L p c hc hc1,
      ∃ chart : ℂ → OpenPartialHomeomorph ℂ ℂ,
        (∀ p, p ∈ (chart p).source) ∧
        (∀ p, (chart p).source ⊆ (model p).chart.source ∧ (chart p : ℂ → ℂ) = (model p).chart) ∧
        ∀ p, ∀ x ∈ (chart p).source, ∀ z ∈ (chart p).source,
          c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (chart p x) (chart p z) ∧
            dist (chart p x) (chart p z) ≤ (pointSmoothConformalEDist a y x z).toReal := by
  classical
  obtain ⟨c, L, hcdef, hc, hc1, hdis, hregular, hbalance, model, hmodel⟩ :=
    point_original_plane_finite_surgery_local_charts ha y
  have hm := fun p : ℂ ↦ (model p).exists_metric_shrink
  choose chart hmem hsource heq hbound using hm
  exact ⟨c, L, hcdef, hc, hc1, hdis, hregular, hbalance, model, chart,
    hmem, fun p ↦ ⟨hsource p, heq p⟩, hbound⟩

end RepulsiveCoulomb
