import LeanResearch.RepulsiveCoulomb.PointIncidentOccupiedMotion
import LeanResearch.RepulsiveCoulomb.PointIncidentChartMetricBounds

/-! SOURCE-ONLY, UNCOMPILED. At an actual point outside all selected closed
sector images, every active refined branch of an incident chart is one of
its constructed unchanged isometries. Finite closedness gives an exact
centered local metric equality even on artificial complement seams. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

namespace PointConstructedIncidentSurgeryChart

/-- Exact equality across all active complement pieces near one point.
Artificial subdivision rays require no special orientation choice. -/
theorem centered_metric_of_no_selected_range
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : ℂ) (hx : x ∈ D.chart.source)
    (hclear : ∀ i : Fin L.length, x ∉ range (L.get i).map) :
    ∀ᶠ z in 𝓝 x,
      dist (D.chart x) (D.chart z) = (pointSmoothConformalEDist a y x z).toReal := by
  let S := pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
    D.data.radius D.refinement
  filter_upwards [finiteClosedFamily_eventually_incident_on_open D.chart.source
    D.chart.open_source S D.source_piece_isClosed x hx] with z hz
  obtain ⟨i, hi⟩ := D.source_piece_cover z hz.1
  have hix := hz.2 i hi
  rcases D.provenance i with ⟨j, hij, _⟩ | ⟨_, hisometry⟩
  · have hei : i = D.occupiedCell j := D.eq_occupiedCell_of_fst_eq i j hij
    have hcell : x ∈ pointRefinedSourceSet
        (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius
        D.refinement (D.occupiedCell j) := hei ▸ hix
    exact False.elim (hclear j.1 ((D.occupied_cell_iff j x (D.source_subset hx)).mp hcell))
  · rw [D.forward_formula i x hx hix, D.forward_formula i z hz.1 hi]
    exact hisometry x ⟨D.source_subset hx, hix⟩ z ⟨D.source_subset hz.1, hi⟩

end PointConstructedIncidentSurgeryChart

namespace PointFiniteSurgeryLocalModel

/-- All three actual chart cases have the original local metric at an
unselected point; the sector-interior case is excluded by actual membership. -/
theorem centered_metric_of_no_selected_range
    (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (x : ℂ) (hx : x ∈ D.chart.source)
    (hclear : ∀ i : Fin L.length, x ∉ range (L.get i).map) :
    ∀ᶠ z in 𝓝 x,
      dist (D.chart x) (D.chart z) = (pointSmoothConformalEDist a y x z).toReal := by
  cases D with
  | sectorInterior i hopen hp =>
      exact False.elim (hclear i ((L.get i).openImage_subset_range hx))
  | unchanged D =>
      filter_upwards [D.chart.open_source.mem_nhds hx] with z hz
      exact D.metric x z hx hz
  | incident D => exact D.centered_metric_of_no_selected_range x hx hclear

end PointFiniteSurgeryLocalModel
end RepulsiveCoulomb
