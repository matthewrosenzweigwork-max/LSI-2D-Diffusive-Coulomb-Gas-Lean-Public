import LeanResearch.RepulsiveCoulomb.TriangularContourNonintersection
import LeanResearch.RepulsiveCoulomb.EmbeddedSimpleGraphCycles
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The canonical finite contour graph itself is an actual straight-line planar
drawing, and each of its simple cycles realizes a Jordan curve. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

def gridContourPlanePosition (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourVertex v t) : Plane :=
  Complex.orthonormalBasisOneI.repr (gridContourPosition v t e)

theorem complex_repr_mem_segment_iff (a b z : ℂ) :
    Complex.orthonormalBasisOneI.repr z ∈ segment ℝ
      (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr b) ↔
    z ∈ segment ℝ a b := by
  have him : Complex.orthonormalBasisOneI.repr '' segment ℝ a b =
      segment ℝ (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr b) :=
    image_segment ℝ Complex.orthonormalBasisOneI.repr.toLinearEquiv.toAffineEquiv.toAffineMap a b
  rw [← him]
  constructor
  · rintro ⟨w, hw, h⟩
    have hwz := Complex.orthonormalBasisOneI.repr.injective h
    exact hwz ▸ hw
  · intro hz
    exact mem_image_of_mem _ hz

theorem gridContourPlanePosition_injective (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) :
    Function.Injective (gridContourPlanePosition v t) :=
  Complex.orthonormalBasisOneI.repr.injective.comp (gridContourPosition_injective v t)

theorem gridContourGraph_isDrawing (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    Graph.IsDrawing (embeddedSimpleGraph (gridContourGraph v t) (gridContourPlanePosition v t))
      (embeddedSimpleDrawing (gridContourPlanePosition v t)) := by
  apply embeddedSimpleGraph_isDrawing _ _ (gridContourPlanePosition_injective v t)
  · intro a b e hab he
    exact gridContourGraph_segment_vertex v ht a b e hab
      ((complex_repr_mem_segment_iff _ _ _).mp he)
  · intro a b c d hab hcd z hzab hzcd
    obtain ⟨w, rfl⟩ := Complex.orthonormalBasisOneI.repr.surjective z
    have hwab := (complex_repr_mem_segment_iff _ _ _).mp hzab
    have hwcd := (complex_repr_mem_segment_iff _ _ _).mp hzcd
    rcases gridContourGraph_segment_intersection v ht a b c d hab hcd hwab hwcd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨e, he, hea, hec⟩ := h
      exact Or.inr (Or.inr ⟨e, congrArg Complex.orthonormalBasisOneI.repr he, hea, hec⟩)

theorem gridContourGraph_cycle_isJordanCurve (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {a : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a a) (hw : w.IsCycle) :
    IsJordanCurve (Graph.edgesCover (embeddedSimpleDrawing (gridContourPlanePosition v t)) w.edges) :=
  embeddedSimpleGraph_cycle_jordan _ _ (gridContourPlanePosition_injective v t)
    (gridContourGraph_isDrawing v ht) w hw

end RepulsiveCoulomb
