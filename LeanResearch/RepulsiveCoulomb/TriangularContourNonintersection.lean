module

public import LeanResearch.RepulsiveCoulomb.TriangularContourVertexIncidence
public import LeanResearch.RepulsiveCoulomb.TriangularGridPointClassification

@[expose] public section

/-! Distinct physical contour edges meet only at their shared contour vertices.
The proof uses the exhaustive physical grid strata, not a planar-graph axiom. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem gridContourGraph_segment_intersection (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (a b c d : GridContourVertex v t)
    (hab : (gridContourGraph v t).Adj a b) (hcd : (gridContourGraph v t).Adj c d)
    {z : ℂ}
    (hzab : z ∈ segment ℝ (gridContourPosition v t a) (gridContourPosition v t b))
    (hzcd : z ∈ segment ℝ (gridContourPosition v t c) (gridContourPosition v t d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨
      ∃ e : GridContourVertex v t, z = gridContourPosition v t e ∧
        (e = a ∨ e = b) ∧ (e = c ∨ e = d) := by
  obtain ⟨i, hi⟩ := gridContourGraph_adj_segment v ht a b hab
  obtain ⟨j, hj⟩ := gridContourGraph_adj_segment v ht c d hcd
  have hzi : z ∈ gridTriangleSlice v i t := hi ▸ hzab
  have hzj : z ∈ gridTriangleSlice v j t := hj ▸ hzcd
  have hir := ((gridTriangleSlice_eq_region_level v i t) ▸ hzi).1
  have hjr := ((gridTriangleSlice_eq_region_level v j t) ▸ hzj).1
  rcases grid_point_classification z with hz | hz | hz
  · obtain ⟨p, rfl⟩ := hz
    have hlevel := gridTriangleSlice_subset_level v i t hzi
    change triangularGridInterpolant v (complexLatticePoint p) = t at hlevel
    rw [triangularGridInterpolant_nodal] at hlevel
    exact (grid_regular_level_ne_node v ht p hlevel).elim
  · obtain ⟨e, he⟩ := hz
    obtain ⟨hc, hpos⟩ := grid_open_edge_level_unique v ht he hzi
    let E : GridContourVertex v t := ⟨e, (mem_gridCrossedEdges v t e).mpr hc⟩
    have hE : z = gridContourPosition v t E := hpos
    right; right
    refine ⟨E, hE, ?_, ?_⟩
    · exact gridContourGraph_segment_vertex v ht a b E hab (hE ▸ hzab)
    · exact gridContourGraph_segment_vertex v ht c d E hcd (hE ▸ hzcd)
  · obtain ⟨k, hk⟩ := hz
    have hik : k = i := gridOpenTriangle_region_unique hk hir
    have hjk : k = j := gridOpenTriangle_region_unique hk hjr
    have hij : i = j := hik.symm.trans hjk
    rw [← hij] at hj
    have hca : gridContourPosition v t c ∈ gridTriangleSlice v i t := by
      rw [hj]; exact left_mem_segment ℝ _ _
    have hda : gridContourPosition v t d ∈ gridTriangleSlice v i t := by
      rw [hj]; exact right_mem_segment ℝ _ _
    rw [hi] at hca hda
    have hc := gridContourGraph_segment_vertex v ht a b c hab hca
    have hd := gridContourGraph_segment_vertex v ht a b d hab hda
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact (hcd.1 rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact (hcd.1 rfl).elim

end RepulsiveCoulomb
