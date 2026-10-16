import LeanResearch.RepulsiveCoulomb.TriangularContourJordanLoops

/-! A finite unoriented-edge carrier for the actual contour, with each physical
segment counted once. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridContourEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : Finset (Sym2 (GridContourVertex v t)) := by
  classical
  exact (gridContourGraph v t).edgeFinset

abbrev GridContourEdge (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) := ↥(gridContourEdges v t)

theorem mem_gridContourEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : Sym2 (GridContourVertex v t)) :
    e ∈ gridContourEdges v t ↔ e ∈ (gridContourGraph v t).edgeSet := by
  classical
  exact SimpleGraph.mem_edgeFinset

def gridContourEdgeStart (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourEdge v t) : ℂ :=
  gridContourPosition v t e.val.out.1

def gridContourEdgeEnd (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourEdge v t) : ℂ :=
  gridContourPosition v t e.val.out.2

theorem gridContourEdge_adj (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourEdge v t) :
    (gridContourGraph v t).Adj e.val.out.1 e.val.out.2 := by
  have he := (mem_gridContourEdges v t e.val).mp e.property
  rw [← sym2_out_pair e.val] at he
  exact he

theorem gridContourEdge_nondegenerate (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourEdge v t) :
    gridContourEdgeStart v t e ≠ gridContourEdgeEnd v t e :=
  (gridContourPosition_injective v t).ne (gridContourEdge_adj v t e).ne

theorem sym2_complex_segment {V : Type*} (p : V → ℂ) {e : Sym2 V} {a b : V}
    (he : e = s(a,b)) :
    segment ℝ (p e.out.1) (p e.out.2) = segment ℝ (p a) (p b) := by
  rcases Sym2.eq_iff.mp ((sym2_out_pair e).trans he) with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb,segment_symm]

theorem gridContourCarrier_eq_edge_union (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) :
    gridContourCarrier v t =
      ⋃ e : GridContourEdge v t, segment ℝ (gridContourEdgeStart v t e) (gridContourEdgeEnd v t e) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨a,hz⟩ := mem_iUnion.mp hz
    obtain ⟨b,hz⟩ := mem_iUnion.mp hz
    obtain ⟨hab,hz⟩ := mem_iUnion.mp hz
    let e : GridContourEdge v t := ⟨s(a,b), (mem_gridContourEdges v t _).mpr hab⟩
    refine mem_iUnion.mpr ⟨e, ?_⟩
    change z ∈ segment ℝ (gridContourPosition v t e.val.out.1) (gridContourPosition v t e.val.out.2)
    rw [sym2_complex_segment (gridContourPosition v t) (show e.val = s(a,b) from rfl)]
    exact hz
  · intro hz
    obtain ⟨e,hz⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨e.val.out.1, mem_iUnion.mpr ⟨e.val.out.2,
      mem_iUnion.mpr ⟨gridContourEdge_adj v t e, hz⟩⟩⟩

theorem gridContourEdges_intersection_finite (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (e f : GridContourEdge v t) (hef : e ≠ f) :
    (segment ℝ (gridContourEdgeStart v t e) (gridContourEdgeEnd v t e) ∩
      segment ℝ (gridContourEdgeStart v t f) (gridContourEdgeEnd v t f)).Finite := by
  apply (finite_range (gridContourPosition v t)).subset
  intro z hz
  rcases gridContourGraph_segment_intersection v ht _ _ _ _
    (gridContourEdge_adj v t e) (gridContourEdge_adj v t f) hz.1 hz.2 with h | h | ⟨a,ha,_,_⟩
  · apply False.elim
    apply hef
    apply Subtype.ext
    calc
      e.val = s(e.val.out.1, e.val.out.2) := (sym2_out_pair e.val).symm
      _ = s(f.val.out.1, f.val.out.2) := congrArg₂ (fun a b => s(a,b)) h.1 h.2
      _ = f.val := sym2_out_pair f.val
  · apply False.elim
    apply hef
    apply Subtype.ext
    calc
      e.val = s(e.val.out.1, e.val.out.2) := (sym2_out_pair e.val).symm
      _ = s(f.val.out.2, f.val.out.1) := congrArg₂ (fun a b => s(a,b)) h.1 h.2
      _ = s(f.val.out.1, f.val.out.2) := Sym2.eq_swap
      _ = f.val := sym2_out_pair f.val
  · exact ⟨a,ha.symm⟩

end RepulsiveCoulomb
