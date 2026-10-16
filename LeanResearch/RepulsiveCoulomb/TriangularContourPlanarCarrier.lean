module

public import LeanResearch.RepulsiveCoulomb.TriangularContourEdgeCarrier

@[expose] public section

/-! The canonical planar drawing occupies exactly the transported physical level,
including its vertices as well as its unoriented edges. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem gridContourDrawing_edgeArc (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (e : Sym2 (GridContourVertex v t)) :
    Graph.edgeArc (embeddedSimpleDrawing (gridContourPlanePosition v t)) e =
      Complex.orthonormalBasisOneI.repr ''
        segment ℝ (gridContourPosition v t e.out.1) (gridContourPosition v t e.out.2) := by
  rw [embeddedSimpleDrawing_arc _ (sym2_out_pair e).symm]
  symm
  exact image_segment ℝ Complex.orthonormalBasisOneI.repr.toLinearEquiv.toAffineEquiv.toAffineMap _ _

theorem gridContourDrawing_pointSet (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    Graph.pointSet (embeddedSimpleGraph (gridContourGraph v t) (gridContourPlanePosition v t))
      (embeddedSimpleDrawing (gridContourPlanePosition v t)) =
      Complex.orthonormalBasisOneI.repr '' ((triangularGridInterpolant v) ⁻¹' {t}) := by
  ext p
  constructor
  · rintro (hp | hp)
    · change p ∈ (gridContourPlanePosition v t) '' univ at hp
      obtain ⟨e,_,rfl⟩ := hp
      exact ⟨gridContourPosition v t e, gridContourPosition_mem_level v ht e, rfl⟩
    · obtain ⟨e,hp⟩ := mem_iUnion.mp hp
      obtain ⟨he,hp⟩ := mem_iUnion.mp hp
      rw [gridContourDrawing_edgeArc] at hp
      obtain ⟨z,hz,rfl⟩ := hp
      change e ∈ (gridContourGraph v t).edgeSet at he
      let E : GridContourEdge v t := ⟨e, (mem_gridContourEdges v t e).mpr he⟩
      have hcarrier : z ∈ gridContourCarrier v t := by
        rw [gridContourCarrier_eq_edge_union]
        exact mem_iUnion.mpr ⟨E,hz⟩
      exact ⟨z, (gridContourCarrier_eq_level v ht) ▸ hcarrier, rfl⟩
  · rintro ⟨z,hz,rfl⟩
    have hcarrier : z ∈ gridContourCarrier v t := (gridContourCarrier_eq_level v ht).symm ▸ hz
    rw [gridContourCarrier_eq_edge_union] at hcarrier
    obtain ⟨e,he⟩ := mem_iUnion.mp hcarrier
    right
    refine mem_iUnion.mpr ⟨e.val, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact (mem_gridContourEdges v t e.val).mp e.property
    · rw [gridContourDrawing_edgeArc]
      exact mem_image_of_mem _ he

end RepulsiveCoulomb
