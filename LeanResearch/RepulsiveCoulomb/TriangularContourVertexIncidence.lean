import LeanResearch.RepulsiveCoulomb.TriangularGridEdgeLevel

/-! A physical contour edge contains no contour vertices other than its actual
endpoints. This supplies the vertex exclusion needed by a planar drawing. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem gridTriangleCrossedEdges_pair_exhausts (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) {a b e : GridEdge}
    (ha : a ∈ gridTriangleCrossedEdges v t i) (hb : b ∈ gridTriangleCrossedEdges v t i)
    (hab : a ≠ b) (he : e ∈ gridTriangleCrossedEdges v t i) : e = a ∨ e = b := by
  by_cases hea : e = a
  · exact Or.inl hea
  · obtain ⟨f, _, _, huniq⟩ := gridTriangle_other_crossed_edge v ht i ha
    exact Or.inr ((huniq e he hea).trans (huniq b hb hab.symm).symm)

theorem gridContourPosition_mem_slice_incidence (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (i : GridTriangle) (e : GridContourVertex v t)
    (he : gridContourPosition v t e ∈ gridTriangleSlice v i t) :
    e.val ∈ gridTriangleCrossedEdges v t i := by
  rw [gridTriangleSlice_eq_region_level] at he
  apply (mem_gridTriangleCrossedEdges v t i e.val).mpr
  exact ⟨grid_open_edge_triangle_incidence
    (gridEdgeLevelPoint_mem_openSegment v t e.val e.property) he.1,
    (mem_gridCrossedEdges v t e.val).mp e.property⟩

theorem gridContourGraph_segment_vertex (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (a b e : GridContourVertex v t)
    (hab : (gridContourGraph v t).Adj a b)
    (he : gridContourPosition v t e ∈
      segment ℝ (gridContourPosition v t a) (gridContourPosition v t b)) :
    e = a ∨ e = b := by
  obtain ⟨hne, i, hai, hbi⟩ := hab
  have ha := (mem_gridTriangleCrossedEdges v t i a.val).mpr
    ⟨hai, (mem_gridCrossedEdges v t a.val).mp a.property⟩
  have hb := (mem_gridTriangleCrossedEdges v t i b.val).mpr
    ⟨hbi, (mem_gridCrossedEdges v t b.val).mp b.property⟩
  have hn : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  have hs := gridTriangleSlice_eq_segment_of_crossed_pair v ht i ha hb hn
  change gridContourPosition v t e ∈ segment ℝ (gridEdgeLevelPoint v t a.val)
    (gridEdgeLevelPoint v t b.val) at he
  rw [← hs] at he
  have hei := gridContourPosition_mem_slice_incidence v i e he
  exact (gridTriangleCrossedEdges_pair_exhausts v ht i ha hb hn hei).imp Subtype.ext Subtype.ext

end RepulsiveCoulomb
