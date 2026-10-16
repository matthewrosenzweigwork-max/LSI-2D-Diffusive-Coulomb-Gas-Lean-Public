import LeanResearch.RepulsiveCoulomb.TriangularGridCrossedTriangles
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! The actual finite contour graph has exactly two neighbors at every vertex.
Its vertices are crossed physical grid edges; adjacency is shared-triangle
incidence. The finite simple cycles are constructed by Mathlib, not assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

abbrev GridContourVertex (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) := ↥(gridCrossedEdges v t)

def gridContourGraph (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : SimpleGraph (GridContourVertex v t) where
  Adj e f := e ≠ f ∧ ∃ i : GridTriangle,
    e.val ∈ range (gridTriangleEdges i) ∧ f.val ∈ range (gridTriangleEdges i)
  symm := ⟨by
    intro e f h
    obtain ⟨hn, i, he, hf⟩ := h
    exact ⟨hn.symm, i, hf, he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

theorem gridContourGraph_two_neighbors (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (e : GridContourVertex v t) :
    ∃ f g : GridContourVertex v t, f ≠ g ∧
      ∀ h : GridContourVertex v t, (gridContourGraph v t).Adj e h ↔ h = f ∨ h = g := by
  have hec := (mem_gridCrossedEdges v t e.val).mp e.property
  have he0 := (mem_gridTriangleCrossedEdges v t (gridEdgeTriangles e.val 0) e.val).mpr
    ⟨gridEdgeTriangles_incident e.val 0, hec⟩
  have he1 := (mem_gridTriangleCrossedEdges v t (gridEdgeTriangles e.val 1) e.val).mpr
    ⟨gridEdgeTriangles_incident e.val 1, hec⟩
  obtain ⟨f, hf, hfe, hfuniq⟩ := gridTriangle_other_crossed_edge v ht _ he0
  obtain ⟨g, hg, hge, hguniq⟩ := gridTriangle_other_crossed_edge v ht _ he1
  have hfc := (mem_gridTriangleCrossedEdges v t _ f).mp hf
  have hgc := (mem_gridTriangleCrossedEdges v t _ g).mp hg
  let F : GridContourVertex v t := ⟨f, (mem_gridCrossedEdges v t f).mpr hfc.2⟩
  let G : GridContourVertex v t := ⟨g, (mem_gridCrossedEdges v t g).mpr hgc.2⟩
  have hfg : F ≠ G := by
    intro h
    have heq : f = g := congrArg Subtype.val h
    have hother : f ∈ range (gridTriangleEdges (gridEdgeTriangles e.val 1)) := by
      rw [heq]; exact hgc.1
    exact hfe (gridEdgeTriangles_common_edge e.val f hfc.1 hother).symm
  have hef : (gridContourGraph v t).Adj e F := by
    refine ⟨?_, gridEdgeTriangles e.val 0, gridEdgeTriangles_incident e.val 0, hfc.1⟩
    intro h
    exact hfe (congrArg Subtype.val h).symm
  have heg : (gridContourGraph v t).Adj e G := by
    refine ⟨?_, gridEdgeTriangles e.val 1, gridEdgeTriangles_incident e.val 1, hgc.1⟩
    intro h
    exact hge (congrArg Subtype.val h).symm
  refine ⟨F, G, hfg, ?_⟩
  intro h
  constructor
  · rintro ⟨hne, i, hei, hhi⟩
    have hhc := (mem_gridCrossedEdges v t h.val).mp h.property
    have hne' : h.val ≠ e.val := by
      intro heq
      exact hne (Subtype.ext heq.symm)
    rcases (grid_triangle_edge_incidence i e.val).mp hei with hi | hi
    · subst i
      have hm := (mem_gridTriangleCrossedEdges v t _ h.val).mpr ⟨hhi, hhc⟩
      exact Or.inl (Subtype.ext (hfuniq h.val hm hne'))
    · subst i
      have hm := (mem_gridTriangleCrossedEdges v t _ h.val).mpr ⟨hhi, hhc⟩
      exact Or.inr (Subtype.ext (hguniq h.val hm hne'))
  · rintro (rfl | rfl)
    · exact hef
    · exact heg

theorem gridContourGraph_neighborSet_card (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (e : GridContourVertex v t) :
    ((gridContourGraph v t).neighborSet e).ncard = 2 := by
  obtain ⟨f, g, hfg, hne⟩ := gridContourGraph_two_neighbors v ht e
  have heq : (gridContourGraph v t).neighborSet e = {f, g} := by
    ext h
    exact hne h
  rw [heq]
  exact Set.ncard_pair hfg

theorem gridContourGraph_isCycles (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) : (gridContourGraph v t).IsCycles := by
  intro e _
  exact gridContourGraph_neighborSet_card v ht e

theorem gridContourGraph_component_cycle (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent)
    (e : GridContourVertex v t) (he : e ∈ c.supp) :
    ∃ p : (gridContourGraph v t).Walk e e, p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  obtain ⟨f, g, hfg, hne⟩ := gridContourGraph_two_neighbors v ht e
  have hn : ((gridContourGraph v t).neighborSet e).Nonempty :=
    ⟨f, (hne f).mpr (Or.inl rfl)⟩
  exact (gridContourGraph_isCycles v ht).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp he hn

end RepulsiveCoulomb
