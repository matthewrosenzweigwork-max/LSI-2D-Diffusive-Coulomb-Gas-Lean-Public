import LeanResearch.RepulsiveCoulomb.TriangularContourPlanarCarrier

/-! Exact physical component carriers, covering the whole contour and disjoint
for distinct graph components. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridContourComponentCarrier (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (c : (gridContourGraph v t).ConnectedComponent) : Set ℂ :=
  ⋃ e : GridContourEdge v t, ⋃ (_ : e.val.out.1 ∈ c.supp),
    segment ℝ (gridContourEdgeStart v t e) (gridContourEdgeEnd v t e)

theorem gridContourComponentCarrier_union (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) :
    (⋃ c, gridContourComponentCarrier v t c) = gridContourCarrier v t := by
  rw [gridContourCarrier_eq_edge_union]
  ext z
  constructor
  · intro hz
    obtain ⟨c,hz⟩ := mem_iUnion.mp hz
    obtain ⟨e,hz⟩ := mem_iUnion.mp hz
    obtain ⟨_,hz⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨e,hz⟩
  · intro hz
    obtain ⟨e,hz⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨(gridContourGraph v t).connectedComponentMk e.val.out.1, ?_⟩
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨rfl,hz⟩⟩

theorem gridContourComponentCarrier_disjoint (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    Pairwise (fun c d => Disjoint (gridContourComponentCarrier v t c) (gridContourComponentCarrier v t d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro z hzc hzd
  obtain ⟨e,hzc⟩ := mem_iUnion.mp hzc
  obtain ⟨he,hzc⟩ := mem_iUnion.mp hzc
  obtain ⟨f,hzd⟩ := mem_iUnion.mp hzd
  obtain ⟨hf,hzd⟩ := mem_iUnion.mp hzd
  have hadj := gridContourEdge_adj v t e
  have hbadj := gridContourEdge_adj v t f
  have he' := (c.mem_supp_congr_adj hadj).mp he
  have hf' := (d.mem_supp_congr_adj hbadj).mp hf
  apply hcd
  rcases gridContourGraph_segment_intersection v ht _ _ _ _ hadj hbadj hzc hzd with h | h | ⟨q,_,hq,hq'⟩
  · exact SimpleGraph.ConnectedComponent.eq_of_common_vertex he (h.1.symm ▸ hf)
  · exact SimpleGraph.ConnectedComponent.eq_of_common_vertex he (h.1.symm ▸ hf')
  · have hqc : q ∈ c.supp := by rcases hq with rfl | rfl <;> assumption
    have hqd : q ∈ d.supp := by rcases hq' with rfl | rfl <;> assumption
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hqc hqd

theorem gridContour_component_cycle_edge_iff (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    {a : GridContourVertex v t} (w : (gridContourGraph v t).Walk a a)
    (hw : w.IsCycle) (hc : w.toSubgraph.verts = c.supp) (e : GridContourEdge v t) :
    e.val ∈ w.edges ↔ e.val.out.1 ∈ c.supp := by
  classical
  letI : (gridContourGraph v t).LocallyFinite := fun _ => Fintype.ofFinite _
  constructor
  · intro he
    rw [← hc, w.mem_verts_toSubgraph]
    rw [← sym2_out_pair e.val] at he
    exact w.fst_mem_support_of_mem_edges he
  · intro he
    have hv : e.val.out.1 ∈ w.toSubgraph.verts := hc.symm ▸ he
    have hadj := (hw.adj_toSubgraph_iff_of_isCycles (gridContourGraph_isCycles v ht) hv _).mpr
      (gridContourEdge_adj v t e)
    have hm := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hadj
    rwa [sym2_out_pair e.val] at hm

end RepulsiveCoulomb
