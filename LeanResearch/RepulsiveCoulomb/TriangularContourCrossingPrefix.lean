import LeanResearch.RepulsiveCoulomb.TriangularContourStepBound
import LeanResearch.RepulsiveCoulomb.FiniteChainFirstExit

/-! A component crossing from B to outside2B has an actual simple full-edge
prefix inside2B, for the unit-mesh approximation stage R>=16. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem gridContourWalkCarrier_subset_level (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {a b : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk a b) :
    gridContourWalkCarrier v t w ⊆ (triangularGridInterpolant v) ⁻¹' {t} := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨j,hj⟩ := gridContourGraph_adj_segment v ht _ _ (w.adj_getVert_succ i.isLt)
  rw [← hj] at hi
  exact gridTriangleSlice_subset_level v j t hi

theorem gridContourComponent_crossing_prefix (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    (x : ℂ) {R : ℝ} (hR : 16 ≤ R)
    (hmeet : (gridContourComponentCarrier v t c ∩ ball x R).Nonempty)
    (hfar : ¬ gridContourComponentCarrier v t c ⊆ ball x (2 * R)) :
    ∃ a b : GridContourVertex v t, ∃ q : (gridContourGraph v t).Walk a b,
      q.IsPath ∧ dist (gridContourPosition v t a) x ≤ 5 * R / 4 ∧
      R / 2 ≤ dist (gridContourPosition v t b) (gridContourPosition v t a) ∧
      gridContourWalkCarrier v t q ⊆ ball x (2 * R) := by
  obtain ⟨z,hzc,hzB⟩ := hmeet
  obtain ⟨a,ha,haz⟩ := gridContourComponent_near_vertex v ht c hzc
  have hstart : dist (gridContourPosition v t a) x ≤ 5 * R / 4 := by
    have hh := dist_triangle (gridContourPosition v t a) z x
    have hz' : dist z x < R := hzB
    linarith
  obtain ⟨b,hb,hbfar⟩ := gridContourComponent_far_vertex v t c x (2 * R) hfar
  obtain ⟨w,hw,hc⟩ := gridContourGraph_component_cycle v ht c a ha
  have hbs : b ∈ w.support := w.mem_verts_toSubgraph.mp (hc.symm ▸ hb)
  obtain ⟨j,hjb,hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbs
  have hfar' : ∃ j ≤ w.length, 7 * R / 4 ≤ dist (gridContourPosition v t (w.getVert j)) x := by
    refine ⟨j,hj,?_⟩
    rw [hjb]
    have hh : 2 * R ≤ dist (gridContourPosition v t b) x := le_of_not_gt hbfar
    linarith
  obtain ⟨k,hkpos,hk,hsep,hball,hseg⟩ := finite_chain_first_exit
    (fun j => gridContourPosition v t (w.getVert j)) w.length x hR
    (by simpa using hstart) hfar'
    (fun j hj => gridContourGraph_adj_dist_le_two v ht _ _ (w.adj_getVert_succ hj))
  have hklt : k < w.length := by
    rcases lt_or_eq_of_le hk with h | h
    · exact h
    · rw [h] at hsep
      simp only [SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero,dist_self] at hsep
      linarith
  refine ⟨a,w.getVert k,w.take k,hw.isPath_take hklt,hstart,?_,?_⟩
  · simpa using hsep
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hil : i.val < k := by simpa [w.take_length, Nat.min_eq_left hk] using i.isLt
    change z ∈ segment ℝ (gridContourPosition v t ((w.take k).getVert i.val))
      (gridContourPosition v t ((w.take k).getVert (i.val + 1))) at hi
    rw [w.take_getVert,w.take_getVert, Nat.min_eq_right (by omega : i.val ≤ k),
      Nat.min_eq_right (by omega : i.val + 1 ≤ k)] at hi
    exact hseg i.val hil hi

end RepulsiveCoulomb
