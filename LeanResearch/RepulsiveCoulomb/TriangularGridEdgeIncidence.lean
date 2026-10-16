import LeanResearch.RepulsiveCoulomb.TriangularGridLocalGeometry

/-! An interior point of a physical grid edge belongs only to the two actual
incident closed grid triangles. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem grid_open_edge_triangle_incidence {e : GridEdge} {i : GridTriangle} {z : ℂ}
    (he : z ∈ openSegment ℝ (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e)))
    (hi : z ∈ gridTriangleRegion i) : e ∈ range (gridTriangleEdges i) := by
  rw [grid_triangle_edge_incidence]
  rw [openSegment_eq_image_lineMap] at he
  obtain ⟨r, hr, rfl⟩ := he
  obtain ⟨hx, hy⟩ := gridEdge_lineMap_coordinates e r
  have hb := gridTriangleRegion_coordinate_bounds hi
  rcases e with ⟨⟨k, l⟩, d⟩
  rcases i with ⟨⟨m, n⟩, b⟩
  fin_cases d <;> dsimp only at hi hb ⊢
  · norm_num at hx hy hb hi ⊢
    rw [hx, hy] at hb
    have hm : m = k := int_cell_fraction_unique k m hr.1 hr.2 (by linarith [hb.1]) (by linarith [hb.2.1])
    have hn : n = l ∨ n = l - 1 := int_cell_integer_options l n (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2])
    subst m
    rcases hn with rfl | rfl <;> cases b <;> solve
      | simp [gridEdgeTriangles]
      | (exfalso
         simp only [complexLatticePoint] at hx hy
         simp [gridTriangleRegion, gridLowerTriangle, gridUpperTriangle, complexLatticePoint,
           hx, hy] at hi
         linarith [hr.1, hr.2, hx, hy])
  · norm_num at hx hy hb hi ⊢
    rw [hx, hy] at hb
    have hm : m = k ∨ m = k - 1 := int_cell_integer_options k m (by linarith [hb.1]) (by linarith [hb.2.1])
    have hn : n = l := int_cell_fraction_unique l n hr.1 hr.2 (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2])
    subst n
    rcases hm with rfl | rfl <;> cases b <;> solve
      | simp [gridEdgeTriangles]
      | (exfalso
         simp only [complexLatticePoint] at hx hy
         simp [gridTriangleRegion, gridLowerTriangle, gridUpperTriangle, complexLatticePoint,
           hx, hy] at hi
         linarith [hr.1, hr.2, hx, hy])
  · norm_num at hx hy hb hi ⊢
    rw [hx, hy] at hb
    have hm : m = k := int_cell_fraction_unique k m hr.1 hr.2 (by linarith [hb.1]) (by linarith [hb.2.1])
    have hn : n = l := int_cell_fraction_unique l n hr.1 hr.2 (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2])
    subst m
    subst n
    cases b <;> simp [gridEdgeTriangles]

end RepulsiveCoulomb
