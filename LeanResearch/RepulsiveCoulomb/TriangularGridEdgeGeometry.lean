module

public import LeanResearch.RepulsiveCoulomb.TriangularContourGraph

@[expose] public section

/-! Exact physical coordinates of open regular-grid edges and injectivity of the
actual contour-vertex position map. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem gridEdge_lineMap_coordinates (e : GridEdge) (r : ℝ) :
    (lineMap (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e)) r).re =
      (e.1.1 : ℝ) + r * (![ (1 : ℝ), 0, 1] e.2) ∧
    (lineMap (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e)) r).im =
      (e.1.2 : ℝ) + r * (![ (0 : ℝ), 1, 1] e.2) := by
  rcases e with ⟨b, d⟩
  fin_cases d <;> constructor <;>
    simp [gridEdgeEnd, complexLatticePoint, lineMap_apply_module, Complex.smul_re, Complex.smul_im] <;> ring

theorem grid_open_edge_floor {e : GridEdge} {z : ℂ}
    (hz : z ∈ openSegment ℝ (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e))) :
    (⌊z.re⌋, ⌊z.im⌋) = e.1 := by
  rcases e with ⟨b, d⟩
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hx, hy⟩ := gridEdge_lineMap_coordinates (b, d) r
  apply Prod.ext
  · rw [hx]
    apply Int.floor_eq_iff.mpr
    fin_cases d <;> norm_num <;> constructor <;> linarith [hr.1, hr.2]
  · rw [hy]
    apply Int.floor_eq_iff.mpr
    fin_cases d <;> norm_num <;> constructor <;> linarith [hr.1, hr.2]

theorem grid_open_edges_unique {e f : GridEdge} {z : ℂ}
    (he : z ∈ openSegment ℝ (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e)))
    (hf : z ∈ openSegment ℝ (complexLatticePoint f.1) (complexLatticePoint (gridEdgeEnd f))) :
    e = f := by
  have hb : e.1 = f.1 := (grid_open_edge_floor he).symm.trans (grid_open_edge_floor hf)
  rcases e with ⟨b, d⟩
  rcases f with ⟨c, k⟩
  change b = c at hb
  subst c
  rw [openSegment_eq_image_lineMap] at he hf
  obtain ⟨r, hr, her⟩ := he
  obtain ⟨s, hs, hfs⟩ := hf
  have hpoint := her.trans hfs.symm
  have hre := congrArg Complex.re hpoint
  have him := congrArg Complex.im hpoint
  rw [(gridEdge_lineMap_coordinates (b, d) r).1, (gridEdge_lineMap_coordinates (b, k) s).1] at hre
  rw [(gridEdge_lineMap_coordinates (b, d) r).2, (gridEdge_lineMap_coordinates (b, k) s).2] at him
  fin_cases d <;> fin_cases k <;> first
    | rfl
    | (exfalso; norm_num at hre <;> norm_num at him <;> linarith [hr.1, hs.1])

def gridContourPosition (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridContourVertex v t) : ℂ :=
  gridEdgeLevelPoint v t e.val

theorem gridContourPosition_injective (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) :
    Function.Injective (gridContourPosition v t) := by
  intro e f h
  have he := gridEdgeLevelPoint_mem_openSegment v t e.val e.property
  have hf := gridEdgeLevelPoint_mem_openSegment v t f.val f.property
  change gridEdgeLevelPoint v t e.val = gridEdgeLevelPoint v t f.val at h
  rw [← h] at hf
  exact Subtype.ext (grid_open_edges_unique he hf)

end RepulsiveCoulomb
