import LeanResearch.RepulsiveCoulomb.TriangularContourWalkCarrier

/-! The ordered physical chain length of a simple contour cycle equals the raw
weighted Hausdorff length of its actual component, without multiplicity. -/
noncomputable section
open Set MeasureTheory AffineMap
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem gridContourWalk_weighted_length {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {u z : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk u z) (hw : w.IsTrail) :
    rawPointLengthMeasure a y (gridContourWalkCarrier v t w) =
      ENNReal.ofReal (rawPointChainLength a y (fun i => gridContourPosition v t (w.getVert i)) w.length) := by
  have h := rawPointLengthMeasure_finite_edges ha y
    (fun i : Fin w.length => gridContourPosition v t (w.getVert i))
    (fun i : Fin w.length => gridContourPosition v t (w.getVert (i + 1)))
    (fun i => (gridContourPosition_injective v t).ne (w.adj_getVert_succ i.isLt).ne)
    (fun i j hij => by
      rw [← segment_eq_image_lineMap, ← segment_eq_image_lineMap,
        ← gridContourWalkEdge_segment, ← gridContourWalkEdge_segment]
      exact gridContourEdges_intersection_finite v ht _ _
        ((gridContourWalkEdge_injective v t w hw).ne hij))
  simp only [← segment_eq_image_lineMap] at h
  change rawPointLengthMeasure a y (gridContourWalkCarrier v t w) = _ at h
  rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => ENNReal.ofReal
    (rawPointSegmentLength a y (gridContourPosition v t (w.getVert i))
      (gridContourPosition v t (w.getVert (i + 1))))) w.length]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => rawPointSegmentLength_nonneg a y _ _)]
  rfl

theorem gridContourCycle_chain_length_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    {u : GridContourVertex v t} (w : (gridContourGraph v t).Walk u u)
    (hw : w.IsCycle) (hc : w.toSubgraph.verts = c.supp) :
    rawPointChainLength a y (fun i => gridContourPosition v t (w.getVert i)) w.length =
      gridContourComponentWeightedLength a y v t c := by
  have h := gridContourWalk_weighted_length ha y v ht w hw.isTrail
  rw [gridContourWalkCarrier_eq_component v ht c w hw hc] at h
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (rawPointChainLength_nonneg a y _ _)] at hh
  exact hh.symm

theorem gridContourComponent_region_area {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (c : (gridContourGraph v t).ConnectedComponent) {U : Set ℂ}
    (hU : Bornology.IsBounded U) (hfront : frontier U ⊆ gridContourComponentCarrier v t c) :
    (rawPointMeasure (fun j => 2 * a j) y).real U ≤
      Real.pi * Real.exp (8 * Q) * gridContourComponentWeightedLength a y v t c ^ 2 := by
  obtain ⟨u,hu⟩ := c.nonempty_supp
  obtain ⟨w,hw,hc⟩ := gridContourGraph_component_cycle v ht c u hu
  rw [← gridContourCycle_chain_length_eq ha y v ht c w hw hc]
  apply pointSquaredRegionArea_le_chainLength_sq ha hQ y _ _ hU
  intro z hz
  have hzc := hfront hz
  rw [← gridContourWalkCarrier_eq_component v ht c w hw hc] at hzc
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzc
  refine ⟨i,i.isLt,?_⟩
  rwa [← segment_eq_image_lineMap]

end RepulsiveCoulomb
