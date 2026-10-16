import LeanResearch.RepulsiveCoulomb.TriangularGridEdgeGeometry

/-! Unified actual triangle geometry and consistency of canonical edge crossings
with the affine formulas on either incident triangle. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridTriangleVertices (i : GridTriangle) : Fin 3 → ℂ :=
  fun j => complexLatticePoint (gridTriangleNodes i j)

def gridTriangleRegion (i : GridTriangle) : Set ℂ :=
  if i.2 then gridUpperTriangle i.1 else gridLowerTriangle i.1

def gridTriangleAffine (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) : ℂ →ᵃ[ℝ] ℝ :=
  if i.2 then gridUpperAffine v i.1 else gridLowerAffine v i.1

theorem gridTriangleVertices_lower (b : ℤ × ℤ) :
    gridTriangleVertices (b, false) = gridLowerVertices b := by
  funext j
  fin_cases j <;> rfl

theorem gridTriangleVertices_upper (b : ℤ × ℤ) :
    gridTriangleVertices (b, true) = gridUpperVertices b := by
  funext j
  fin_cases j <;> rfl

theorem gridTriangleVertices_affineIndependent (i : GridTriangle) :
    AffineIndependent ℝ (gridTriangleVertices i) := by
  rcases i with ⟨b, k⟩
  cases k
  · rw [gridTriangleVertices_lower]
    exact gridLowerVertices_affineIndependent b
  · rw [gridTriangleVertices_upper]
    exact gridUpperVertices_affineIndependent b

theorem gridTriangleRegion_convexHull (i : GridTriangle) :
    gridTriangleRegion i = convexHull ℝ (range (gridTriangleVertices i)) := by
  rcases i with ⟨b, k⟩
  cases k
  · rw [gridTriangleVertices_lower]
    exact gridLowerTriangle_eq_convexHull b
  · rw [gridTriangleVertices_upper]
    exact gridUpperTriangle_eq_convexHull b

theorem gridTriangleAffine_vertex_values (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) (j : Fin 3) :
    gridTriangleAffine v i (gridTriangleVertices i j) = v (gridTriangleNodes i j) := by
  rcases i with ⟨b, k⟩
  cases k
  · rw [gridTriangleVertices_lower]
    change gridLowerAffine v b (gridLowerVertices b j) = _
    rw [gridLowerAffine_vertex_values]
    fin_cases j <;> rfl
  · rw [gridTriangleVertices_upper]
    change gridUpperAffine v b (gridUpperVertices b j) = _
    rw [gridUpperAffine_vertex_values]
    fin_cases j <;> rfl

theorem gridTriangleSlice_eq_region_level (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) (t : ℝ) :
    gridTriangleSlice v i t = gridTriangleRegion i ∩ (gridTriangleAffine v i) ⁻¹' {t} := by
  rcases i with ⟨b, k⟩
  cases k <;> rfl

theorem gridTriangle_edge_levelPoint (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (i : GridTriangle) (j : Fin 3) (hc : gridEdgeCrosses v t (gridTriangleEdges i j)) :
    gridEdgeLevelPoint v t (gridTriangleEdges i j) =
      affineLevelEdgePoint (gridTriangleVertices i j) (gridTriangleVertices i (j + 1))
        (gridTriangleAffine v i (gridTriangleVertices i j))
        (gridTriangleAffine v i (gridTriangleVertices i (j + 1))) t := by
  rw [gridTriangleAffine_vertex_values, gridTriangleAffine_vertex_values]
  rcases i with ⟨⟨x, y⟩, k⟩
  cases k <;> fin_cases j <;>
    simp [gridEdgeLevelPoint, gridTriangleEdges, gridTriangleVertices, gridTriangleNodes,
      gridEdgeEnd, gridEdgeCrosses, add_assoc] at hc ⊢
  all_goals first
    | rfl
    | (apply (affineLevelEdgePoint_reverse _ _ ?_ t).symm
       rcases hc with hc | hc <;> linarith [hc.1, hc.2])

theorem gridCrossedEdgePoint_mem_triangle_slice (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) {e : GridEdge}
    (he : e ∈ gridTriangleCrossedEdges v t i) :
    gridEdgeLevelPoint v t e ∈ gridTriangleSlice v i t := by
  obtain ⟨⟨j, rfl⟩, hc⟩ := (mem_gridTriangleCrossedEdges v t i e).mp he
  have hj := (gridTriangle_crossing_iff v ht i j).mp hc
  have hs := (triangleCrossingEdges_mem_iff (fun k => grid_regular_level_ne_node v ht _) j).mp hj
  rw [gridTriangle_edge_levelPoint v t i j hc, gridTriangleSlice_eq_region_level]
  refine ⟨?_, affineLevelEdgePoint_apply (gridTriangleAffine v i)
    (gridTriangleVertices i j) (gridTriangleVertices i (j + 1)) ?_ t⟩
  · rw [gridTriangleRegion_convexHull]
    apply (convex_convexHull ℝ (range (gridTriangleVertices i))).segment_subset
      (subset_convexHull ℝ _ (mem_range_self j))
      (subset_convexHull ℝ _ (mem_range_self (j + 1)))
    apply openSegment_subset_segment ℝ _ _
    apply affineLevelEdgePoint_mem_openSegment
    simpa only [gridTriangleAffine_vertex_values] using hs
  · rw [gridTriangleAffine_vertex_values, gridTriangleAffine_vertex_values]
    rcases hs with hs | hs <;> linarith [hs.1, hs.2]

end RepulsiveCoulomb
