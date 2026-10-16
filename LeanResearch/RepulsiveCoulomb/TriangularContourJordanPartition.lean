import LeanResearch.RepulsiveCoulomb.TriangularContourComponents

/-! Exact pairwise-disjoint polygonal Jordan decomposition of every regular
finite-grid level, indexed by its genuinely finite graph components. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem gridContour_component_cycle_carrier (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    {a : GridContourVertex v t} (w : (gridContourGraph v t).Walk a a)
    (hw : w.IsCycle) (hc : w.toSubgraph.verts = c.supp) :
    Graph.edgesCover (embeddedSimpleDrawing (gridContourPlanePosition v t)) w.edges =
      Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c := by
  ext p
  constructor
  · intro hp
    obtain ⟨e,he,hp⟩ := Graph.mem_edgesCover_iff.mp hp
    let E : GridContourEdge v t := ⟨e, (mem_gridContourEdges v t e).mpr (w.edges_subset_edgeSet he)⟩
    have hec := (gridContour_component_cycle_edge_iff v ht c w hw hc E).mp he
    rw [gridContourDrawing_edgeArc] at hp
    obtain ⟨z,hz,rfl⟩ := hp
    refine ⟨z, ?_, rfl⟩
    exact mem_iUnion.mpr ⟨E, mem_iUnion.mpr ⟨hec,hz⟩⟩
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨e,hz⟩ := mem_iUnion.mp hz
    obtain ⟨hec,hz⟩ := mem_iUnion.mp hz
    apply Graph.mem_edgesCover ((gridContour_component_cycle_edge_iff v ht c w hw hc e).mpr hec)
    rw [gridContourDrawing_edgeArc]
    exact mem_image_of_mem _ hz

theorem gridContourComponent_isJordan_polygon (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    IsJordanCurve (Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c) ∧
    IsPolygonal (Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c) := by
  obtain ⟨a,ha⟩ := c.nonempty_supp
  obtain ⟨w,hw,hc⟩ := gridContourGraph_component_cycle v ht c a ha
  rw [← gridContour_component_cycle_carrier v ht c w hw hc]
  exact ⟨gridContourGraph_cycle_isJordanCurve v ht w hw, gridContourGraph_cycle_isPolygonal v ht w hw⟩

theorem gridContourComponent_plane_disjoint (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    Pairwise (fun c d => Disjoint
      (Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c)
      (Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  rintro p ⟨z,hz,hzp⟩ ⟨w,hw,hwp⟩
  have hzw := Complex.orthonormalBasisOneI.repr.injective (hzp.trans hwp.symm)
  subst w
  exact Set.disjoint_left.mp (gridContourComponentCarrier_disjoint v ht hcd) hz hw

theorem gridContourComponent_plane_union (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    (⋃ c : (gridContourGraph v t).ConnectedComponent,
      Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c) =
      Complex.orthonormalBasisOneI.repr '' ((triangularGridInterpolant v) ⁻¹' {t}) := by
  rw [← image_iUnion, gridContourComponentCarrier_union, gridContourCarrier_eq_level v ht]

end RepulsiveCoulomb
