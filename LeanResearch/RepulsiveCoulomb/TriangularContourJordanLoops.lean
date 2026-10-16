import LeanResearch.RepulsiveCoulomb.TriangularContourPlanarDrawing

/-! Actual polygonal Jordan realizations of the finite contour component cycles. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem embeddedSimpleGraph_walk {V : Type*} (G : SimpleGraph V) (p : V → Plane)
    {a b : V} (w : G.Walk a b) :
    (embeddedSimpleGraph G p).IsWalk (p a) w.edges (p b) := by
  induction w with
  | nil => exact .nil (embeddedSimpleGraph_vertex G p _)
  | cons h _ ih => exact .cons (embeddedSimpleGraph_link G p h) ih

theorem embeddedSimpleDrawing_edge_polygonal {V : Type*} (p : V → Plane) (e : Sym2 V) :
    IsPolygonal (Graph.edgeArc (embeddedSimpleDrawing p) e) := by
  rw [embeddedSimpleDrawing_arc p (sym2_out_pair e).symm]
  exact isPolygonal_segment _ _

theorem gridContourGraph_cycle_isPolygonal (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {a : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a a) (hw : w.IsCycle) :
    IsPolygonal (Graph.edgesCover (embeddedSimpleDrawing (gridContourPlanePosition v t)) w.edges) := by
  apply (gridContourGraph_isDrawing v ht).isPolygonal_edgesCover
    (fun e _ => embeddedSimpleDrawing_edge_polygonal _ e)
    (embeddedSimpleGraph_walk _ _ w)
  exact fun h => hw.not_nil (SimpleGraph.Walk.edges_eq_nil.mp h)

theorem gridContourGraph_component_jordan_polygon (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    (a : GridContourVertex v t) (ha : a ∈ c.supp) :
    ∃ w : (gridContourGraph v t).Walk a a, w.IsCycle ∧ w.toSubgraph.verts = c.supp ∧
      IsJordanCurve (Graph.edgesCover (embeddedSimpleDrawing (gridContourPlanePosition v t)) w.edges) ∧
      IsPolygonal (Graph.edgesCover (embeddedSimpleDrawing (gridContourPlanePosition v t)) w.edges) := by
  obtain ⟨w, hw, hc⟩ := gridContourGraph_component_cycle v ht c a ha
  exact ⟨w, hw, hc, gridContourGraph_cycle_isJordanCurve v ht w hw,
    gridContourGraph_cycle_isPolygonal v ht w hw⟩

end RepulsiveCoulomb
