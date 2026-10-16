import LeanResearch.RepulsiveCoulomb.TriangularContourComponentLength
import LeanResearch.RepulsiveCoulomb.PointWeightedPolygonalChain

/-! The actual ordered vertex chain of a contour walk and its exact physical
carrier, with no repeated unoriented edges for trails. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridContourWalkEdge (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) (i : Fin w.length) : GridContourEdge v t :=
  ⟨s(w.getVert i, w.getVert (i + 1)), (mem_gridContourEdges v t _).mpr (w.adj_getVert_succ i.isLt)⟩

theorem gridContourWalkEdge_mem (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) (i : Fin w.length) :
    (gridContourWalkEdge v t w i).val ∈ w.edges := by
  exact (w.mk_mem_edges_iff_exists).mpr ⟨i, i.isLt, rfl⟩

theorem gridContourWalkEdge_injective (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) (hw : w.IsTrail) :
    Function.Injective (gridContourWalkEdge v t w) := by
  intro i j h
  have hi : i.val < w.edges.length := by simpa using i.isLt
  have hj : j.val < w.edges.length := by simpa using j.isLt
  have he : w.edges[i.val] = w.edges[j.val] := by
    rw [SimpleGraph.Walk.getElem_edges hi, SimpleGraph.Walk.getElem_edges hj]
    exact congrArg Subtype.val h
  exact Fin.ext (hw.edges_nodup.getElem_inj_iff.mp he)

theorem gridContourWalkEdge_segment (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) (i : Fin w.length) :
    segment ℝ (gridContourEdgeStart v t (gridContourWalkEdge v t w i))
      (gridContourEdgeEnd v t (gridContourWalkEdge v t w i)) =
    segment ℝ (gridContourPosition v t (w.getVert i)) (gridContourPosition v t (w.getVert (i + 1))) :=
  sym2_complex_segment (gridContourPosition v t) rfl

def gridContourWalkCarrier (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) : Set ℂ :=
  ⋃ i : Fin w.length, segment ℝ (gridContourPosition v t (w.getVert i))
    (gridContourPosition v t (w.getVert (i + 1)))

theorem gridContourWalkCarrier_eq_component (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    {a : GridContourVertex v t} (w : (gridContourGraph v t).Walk a a)
    (hw : w.IsCycle) (hc : w.toSubgraph.verts = c.supp) :
    gridContourWalkCarrier v t w = gridContourComponentCarrier v t c := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,hz⟩ := mem_iUnion.mp hz
    let e := gridContourWalkEdge v t w i
    have hm := gridContourWalkEdge_mem v t w i
    have he := (gridContour_component_cycle_edge_iff v ht c w hw hc e).mp hm
    refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, ?_⟩⟩
    rw [gridContourWalkEdge_segment]
    exact hz
  · intro hz
    obtain ⟨e,hz⟩ := mem_iUnion.mp hz
    obtain ⟨he,hz⟩ := mem_iUnion.mp hz
    have hm := (gridContour_component_cycle_edge_iff v ht c w hw hc e).mpr he
    obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hm
    let I : Fin w.length := ⟨i, by simpa using hi⟩
    refine mem_iUnion.mpr ⟨I, ?_⟩
    have heq' : e.val = s(w.getVert i, w.getVert (i + 1)) := by
      rw [← heq, SimpleGraph.Walk.getElem_edges hi]
    have hs := sym2_complex_segment (gridContourPosition v t) heq'
    change z ∈ segment ℝ (gridContourPosition v t e.val.out.1) (gridContourPosition v t e.val.out.2) at hz
    rw [hs] at hz
    exact hz

end RepulsiveCoulomb
