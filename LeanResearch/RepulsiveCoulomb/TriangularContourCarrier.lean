import LeanResearch.RepulsiveCoulomb.TriangularCanonicalSegments

/-! Exact equality between the physical carrier of the constructed finite contour
graph and the actual interpolant level. No geometric nonintersection is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridContourCarrier (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : Set ℂ :=
  ⋃ e : GridContourVertex v t, ⋃ f : GridContourVertex v t,
    ⋃ (_ : (gridContourGraph v t).Adj e f),
      segment ℝ (gridContourPosition v t e) (gridContourPosition v t f)

theorem gridTriangleSlice_subset_level (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) (t : ℝ) :
    gridTriangleSlice v i t ⊆ (triangularGridInterpolant v) ⁻¹' {t} := by
  rcases i with ⟨b, k⟩
  cases k
  · intro z hz
    exact (triangularGridInterpolant_eq_lowerAffine v b hz.1).trans hz.2
  · intro z hz
    exact (triangularGridInterpolant_eq_upperAffine v b hz.1).trans hz.2

theorem gridContourCarrier_eq_level (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    gridContourCarrier v t = (triangularGridInterpolant v) ⁻¹' {t} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨f, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hadj, hz⟩ := mem_iUnion.mp hz
    obtain ⟨i, hi⟩ := gridContourGraph_adj_segment v ht e f hadj
    rw [← hi] at hz
    exact gridTriangleSlice_subset_level v i t hz
  · intro hz
    rw [triangularGridInterpolant_level_union_slices v (grid_regular_level_ne_zero v ht)] at hz
    obtain ⟨i, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    rcases gridTriangleSlice_empty_or_crossed_segment v ht i with hempty | ⟨e, f, he, hf, hef, hs⟩
    · rw [hempty] at hz
      exact hz.elim
    · have hec := (mem_gridTriangleCrossedEdges v t i e).mp he
      have hfc := (mem_gridTriangleCrossedEdges v t i f).mp hf
      let E : GridContourVertex v t := ⟨e, (mem_gridCrossedEdges v t e).mpr hec.2⟩
      let F : GridContourVertex v t := ⟨f, (mem_gridCrossedEdges v t f).mpr hfc.2⟩
      have hadj : (gridContourGraph v t).Adj E F := by
        refine ⟨?_, i, hec.1, hfc.1⟩
        exact fun h => hef (congrArg Subtype.val h)
      refine mem_iUnion.mpr ⟨E, mem_iUnion.mpr ⟨F, mem_iUnion.mpr ⟨hadj, ?_⟩⟩⟩
      change z ∈ segment ℝ (gridEdgeLevelPoint v t e) (gridEdgeLevelPoint v t f)
      rw [← hs]
      exact hz

theorem gridContourPosition_mem_level (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (e : GridContourVertex v t) :
    triangularGridInterpolant v (gridContourPosition v t e) = t := by
  have he := (mem_gridTriangleCrossedEdges v t (gridEdgeTriangles e.val 0) e.val).mpr
    ⟨gridEdgeTriangles_incident e.val 0, (mem_gridCrossedEdges v t e.val).mp e.property⟩
  exact gridTriangleSlice_subset_level v _ t (gridCrossedEdgePoint_mem_triangle_slice v ht _ he)

theorem gridContourCarrier_disjoint_lattice (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    Disjoint (gridContourCarrier v t) (range complexLatticePoint) := by
  rw [gridContourCarrier_eq_level v ht]
  apply Set.disjoint_left.mpr
  rintro z hz ⟨p, rfl⟩
  change triangularGridInterpolant v (complexLatticePoint p) = t at hz
  rw [triangularGridInterpolant_nodal] at hz
  exact grid_regular_level_ne_node v ht p hz

end RepulsiveCoulomb
