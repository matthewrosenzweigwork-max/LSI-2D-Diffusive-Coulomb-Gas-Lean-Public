module

public import LeanResearch.RepulsiveCoulomb.TriangularContourCarrier
public import LeanResearch.RepulsiveCoulomb.TriangularGridEdgeIncidence

@[expose] public section

/-! Actual endpoint values and uniqueness of a regular level crossing on a
physical grid edge, with no assumed geometric realization. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem gridTriangleAffine_edge_values (v : (ℤ × ℤ) →₀ ℝ) {i : GridTriangle} {e : GridEdge}
    (he : e ∈ range (gridTriangleEdges i)) :
    gridTriangleAffine v i (complexLatticePoint e.1) = v e.1 ∧
    gridTriangleAffine v i (complexLatticePoint (gridEdgeEnd e)) = v (gridEdgeEnd e) := by
  obtain ⟨j, rfl⟩ := he
  rcases i with ⟨⟨k, l⟩, b⟩
  cases b <;> fin_cases j <;>
    simp [gridTriangleAffine, gridTriangleEdges, gridEdgeEnd, gridLowerAffine_apply,
      gridUpperAffine_apply, complexLatticePoint] <;> ring

theorem strict_affine_average_straddles {a b t r : ℝ} (hr : r ∈ Ioo 0 1)
    (ha : a ≠ t) (ht : (1-r)*a + r*b = t) :
    (a < t ∧ t < b) ∨ (b < t ∧ t < a) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · left
    refine ⟨ha, ?_⟩
    nlinarith [mul_pos hr.1 (sub_pos.mpr ha), mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr ha)]
  · right
    refine ⟨?_, ha⟩
    nlinarith [mul_pos hr.1 (sub_pos.mpr ha), mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr ha)]

theorem grid_open_edge_level_unique (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {e : GridEdge} {i : GridTriangle} {z : ℂ}
    (he : z ∈ openSegment ℝ (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e)))
    (hz : z ∈ gridTriangleSlice v i t) :
    gridEdgeCrosses v t e ∧ z = gridEdgeLevelPoint v t e := by
  rw [gridTriangleSlice_eq_region_level] at hz
  have hi := grid_open_edge_triangle_incidence he hz.1
  obtain ⟨ha, hb⟩ := gridTriangleAffine_edge_values v hi
  have hne : v e.1 ≠ t := grid_regular_level_ne_node v ht _
  have hc : gridEdgeCrosses v t e := by
    rw [openSegment_eq_image_lineMap] at he
    obtain ⟨r, hr, rfl⟩ := he
    have h := hz.2
    change gridTriangleAffine v i (lineMap _ _ r) = t at h
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module, ha, hb] at h
    simp only [smul_eq_mul] at h
    exact strict_affine_average_straddles hr hne h
  refine ⟨hc, ?_⟩
  have hab : v e.1 ≠ v (gridEdgeEnd e) := by
    rcases hc with hc | hc <;> linarith [hc.1, hc.2]
  have h := affineLevelEdgePoint_unique (gridTriangleAffine v i)
    (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e))
    (by rw [ha, hb]; exact hab) (openSegment_subset_segment ℝ _ _ he) hz.2
  simpa only [ha, hb, gridEdgeLevelPoint] using h

end RepulsiveCoulomb
