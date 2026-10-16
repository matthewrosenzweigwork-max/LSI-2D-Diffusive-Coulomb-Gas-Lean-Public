module

public import LeanResearch.RepulsiveCoulomb.TriangularContourRelativeSign

@[expose] public section

/-! Unit-grid contour edges have physical diameter at most2. These explicit
mesh bounds will remove clipping from the localized crossing-chain argument. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem gridTriangleRegion_dist_le_two {i : GridTriangle} {z w : ℂ}
    (hz : z ∈ gridTriangleRegion i) (hw : w ∈ gridTriangleRegion i) : dist z w ≤ 2 := by
  have hzB := gridTriangleRegion_coordinate_bounds hz
  have hwB := gridTriangleRegion_coordinate_bounds hw
  have hx : |z.re - w.re| ≤ 1 := abs_le.mpr ⟨by linarith [hzB.1,hwB.2.1], by linarith [hwB.1,hzB.2.1]⟩
  have hy : |z.im - w.im| ≤ 1 := abs_le.mpr ⟨by linarith [hzB.2.2.1,hwB.2.2.2], by linarith [hwB.2.2.1,hzB.2.2.2]⟩
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (z-w)
  simp only [Complex.sub_re,Complex.sub_im] at hn
  linarith

theorem gridContourGraph_segment_diameter (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (a b : GridContourVertex v t)
    (hab : (gridContourGraph v t).Adj a b) {x y : ℂ}
    (hx : x ∈ segment ℝ (gridContourPosition v t a) (gridContourPosition v t b))
    (hy : y ∈ segment ℝ (gridContourPosition v t a) (gridContourPosition v t b)) : dist x y ≤ 2 := by
  obtain ⟨i,hi⟩ := gridContourGraph_adj_segment v ht a b hab
  rw [← hi,gridTriangleSlice_eq_region_level] at hx hy
  exact gridTriangleRegion_dist_le_two hx.1 hy.1

theorem gridContourGraph_adj_dist_le_two (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (a b : GridContourVertex v t)
    (hab : (gridContourGraph v t).Adj a b) : dist (gridContourPosition v t a) (gridContourPosition v t b) ≤ 2 :=
  gridContourGraph_segment_diameter v ht a b hab (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)

theorem gridContourComponent_near_vertex (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    {z : ℂ} (hz : z ∈ gridContourComponentCarrier v t c) :
    ∃ a : GridContourVertex v t, a ∈ c.supp ∧ dist (gridContourPosition v t a) z ≤ 2 := by
  obtain ⟨e,hz⟩ := mem_iUnion.mp hz
  obtain ⟨he,hz⟩ := mem_iUnion.mp hz
  exact ⟨e.val.out.1,he,gridContourGraph_segment_diameter v ht _ _ (gridContourEdge_adj v t e)
    (left_mem_segment ℝ _ _) hz⟩

theorem gridContourComponent_ball_of_vertices (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (c : (gridContourGraph v t).ConnectedComponent) (x : ℂ) (R : ℝ)
    (h : ∀ a ∈ c.supp, gridContourPosition v t a ∈ ball x R) :
    gridContourComponentCarrier v t c ⊆ ball x R := by
  intro z hz
  obtain ⟨e,hz⟩ := mem_iUnion.mp hz
  obtain ⟨he,hz⟩ := mem_iUnion.mp hz
  have he' := (c.mem_supp_congr_adj (gridContourEdge_adj v t e)).mp he
  exact (convex_ball x R).segment_subset (h _ he) (h _ he') hz

theorem gridContourComponent_far_vertex (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (c : (gridContourGraph v t).ConnectedComponent) (x : ℂ) (R : ℝ)
    (h : ¬ gridContourComponentCarrier v t c ⊆ ball x R) :
    ∃ a : GridContourVertex v t, a ∈ c.supp ∧ gridContourPosition v t a ∉ ball x R := by
  classical
  by_contra hh
  push_neg at hh
  exact h (gridContourComponent_ball_of_vertices v t c x R hh)

end RepulsiveCoulomb
