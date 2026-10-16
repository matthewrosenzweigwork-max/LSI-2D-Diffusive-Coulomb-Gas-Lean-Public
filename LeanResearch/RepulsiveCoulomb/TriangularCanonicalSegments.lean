module

public import LeanResearch.RepulsiveCoulomb.TriangularContourGeometry

@[expose] public section

/-! The actual geometric segment of a regular grid triangle has exactly the two
canonical crossed-edge points as endpoints. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem gridTriangleSlice_empty_or_crossed_segment (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) :
    gridTriangleSlice v i t = ∅ ∨ ∃ e f : GridEdge,
      e ∈ gridTriangleCrossedEdges v t i ∧ f ∈ gridTriangleCrossedEdges v t i ∧ e ≠ f ∧
      gridTriangleSlice v i t = segment ℝ (gridEdgeLevelPoint v t e) (gridEdgeLevelPoint v t f) := by
  have hnode : ∀ j, gridTriangleAffine v i (gridTriangleVertices i j) ≠ t := by
    intro j
    rw [gridTriangleAffine_vertex_values]
    exact grid_regular_level_ne_node v ht _
  have h := affine_triangle_regular_level (gridTriangleAffine v i) (gridTriangleVertices i)
    (gridTriangleVertices_affineIndependent i).injective t hnode
  have hslice : gridTriangleSlice v i t =
      convexHull ℝ ({gridTriangleVertices i 0, gridTriangleVertices i 1, gridTriangleVertices i 2} : Set ℂ) ∩
        (gridTriangleAffine v i) ⁻¹' {t} := by
    rw [gridTriangleSlice_eq_region_level, gridTriangleRegion_convexHull, range_fin3_eq_triple]
  rw [← hslice] at h
  rcases h with h | ⟨k, h1, h2, hseg⟩
  · exact Or.inl h
  · have h1n := h1
    have h2n := h2
    simp only [gridTriangleAffine_vertex_values] at h1n h2n
    have hk : (k + 2) + 1 = k := by fin_cases k <;> decide
    have hc0 : gridEdgeCrosses v t (gridTriangleEdges i k) := by
      apply (gridTriangle_crossing_iff v ht i k).mpr
      exact (triangleCrossingEdges_mem_iff (fun j => grid_regular_level_ne_node v ht _) k).mpr h1n
    have hc1 : gridEdgeCrosses v t (gridTriangleEdges i (k + 2)) := by
      apply (gridTriangle_crossing_iff v ht i (k + 2)).mpr
      apply (triangleCrossingEdges_mem_iff (fun j => grid_regular_level_ne_node v ht _) (k + 2)).mpr
      rw [hk]
      exact h2n.symm
    have hp0 := gridTriangle_edge_levelPoint v t i k hc0
    have hp1 := gridTriangle_edge_levelPoint v t i (k + 2) hc1
    rw [hk] at hp1
    have hneval : gridTriangleAffine v i (gridTriangleVertices i k) ≠
        gridTriangleAffine v i (gridTriangleVertices i (k + 2)) := by
      rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2]
    rw [affineLevelEdgePoint_reverse _ _ hneval t] at hp1
    rw [← hp0, ← hp1] at hseg
    refine Or.inr ⟨gridTriangleEdges i k, gridTriangleEdges i (k + 2), ?_, ?_, ?_, hseg⟩
    · exact (mem_gridTriangleCrossedEdges v t i _).mpr ⟨mem_range_self _, hc0⟩
    · exact (mem_gridTriangleCrossedEdges v t i _).mpr ⟨mem_range_self _, hc1⟩
    · exact (gridTriangleEdges_injective i).ne (by fin_cases k <;> decide)

theorem gridTriangleSlice_eq_segment_of_crossed_pair (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) {e f : GridEdge}
    (he : e ∈ gridTriangleCrossedEdges v t i) (hf : f ∈ gridTriangleCrossedEdges v t i)
    (hef : e ≠ f) :
    gridTriangleSlice v i t = segment ℝ (gridEdgeLevelPoint v t e) (gridEdgeLevelPoint v t f) := by
  classical
  rcases gridTriangleSlice_empty_or_crossed_segment v ht i with hz | ⟨a, b, ha, hb, hab, hs⟩
  · have hp := gridCrossedEdgePoint_mem_triangle_slice v ht i he
    rw [hz] at hp
    exact hp.elim
  · have hsub : ({a, b} : Finset GridEdge) ⊆ gridTriangleCrossedEdges v t i := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact Finset.mem_singleton.mp hx ▸ hb
    have hcard : (gridTriangleCrossedEdges v t i).card ≤ 2 := by
      rcases gridTriangleCrossedEdges_card v ht i with h | h <;> rw [h] <;> norm_num
    have heq : ({a, b} : Finset GridEdge) = gridTriangleCrossedEdges v t i :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hab] using hcard)
    rw [← heq] at he hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hef rfl).elim
    · exact hs
    · exact hs.trans (segment_symm ℝ _ _)
    · exact (hef rfl).elim

theorem gridContourGraph_adj_segment (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (e f : GridContourVertex v t)
    (hadj : (gridContourGraph v t).Adj e f) :
    ∃ i : GridTriangle, gridTriangleSlice v i t =
      segment ℝ (gridContourPosition v t e) (gridContourPosition v t f) := by
  obtain ⟨hne, i, hei, hfi⟩ := hadj
  refine ⟨i, gridTriangleSlice_eq_segment_of_crossed_pair v ht i ?_ ?_ ?_⟩
  · exact (mem_gridTriangleCrossedEdges v t i _).mpr
      ⟨hei, (mem_gridCrossedEdges v t e.val).mp e.property⟩
  · exact (mem_gridTriangleCrossedEdges v t i _).mpr
      ⟨hfi, (mem_gridCrossedEdges v t f.val).mp f.property⟩
  · exact fun h => hne (Subtype.ext h)

end RepulsiveCoulomb
