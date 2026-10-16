module

public import LeanResearch.RepulsiveCoulomb.TriangularGridNullLines

@[expose] public section

/-! Almost every physical point lies in an open triangle for every mesh in a
specified countable positive mesh sequence. -/
noncomputable section
open Set MeasureTheory AffineMap
namespace RepulsiveCoulomb

theorem complexLatticePoint_mem_skeleton (p : ℤ × ℤ) : complexLatticePoint p ∈ unitGridSkeleton := by
  exact mem_iUnion.mpr ⟨p.1,mem_iUnion.mpr ⟨0,rfl⟩⟩

theorem grid_open_edge_mem_skeleton {e : GridEdge} {z : ℂ}
    (he : z ∈ openSegment ℝ (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e))) :
    z ∈ unitGridSkeleton := by
  rw [openSegment_eq_image_lineMap] at he
  obtain ⟨r,_,rfl⟩ := he
  rcases e with ⟨b,d⟩
  obtain ⟨hx,hy⟩ := gridEdge_lineMap_coordinates (b,d) r
  fin_cases d
  · norm_num at hx hy
    refine mem_iUnion.mpr ⟨b.2,mem_iUnion.mpr ⟨1,?_⟩⟩
    exact hy
  · norm_num at hx hy
    refine mem_iUnion.mpr ⟨b.1,mem_iUnion.mpr ⟨0,?_⟩⟩
    exact hx
  · norm_num at hx hy
    refine mem_iUnion.mpr ⟨b.1-b.2,mem_iUnion.mpr ⟨2,?_⟩⟩
    change ((lineMap (complexLatticePoint b) (complexLatticePoint (gridEdgeEnd (b,2)))) r).re -
      ((lineMap (complexLatticePoint b) (complexLatticePoint (gridEdgeEnd (b,2)))) r).im = ↑(b.1-b.2)
    rw [hx,hy,Int.cast_sub]
    ring

theorem grid_open_triangle_of_not_skeleton {z : ℂ} (hz : z ∉ unitGridSkeleton) :
    ∃ i : GridTriangle, z ∈ gridOpenTriangle i := by
  rcases grid_point_classification z with ⟨p,rfl⟩ | ⟨e,he⟩ | h
  · exact (hz (complexLatticePoint_mem_skeleton p)).elim
  · exact (hz (grid_open_edge_mem_skeleton he)).elim
  · exact h

theorem grid_sequence_ae_open_triangles (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) :
    ∀ᵐ z : ℂ ∂volume, ∀ n : ℕ, ∃ i : GridTriangle, (h n)⁻¹ • z ∈ gridOpenTriangle i := by
  have hgood : ∀ᵐ z : ℂ ∂volume, z ∉ gridSequenceSkeleton h := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_mem_eq] using gridSequenceSkeleton_volume_zero h
  filter_upwards [hgood] with z hz
  intro n
  apply grid_open_triangle_of_not_skeleton
  intro hunit
  obtain ⟨k,hunit⟩ := mem_iUnion.mp hunit
  obtain ⟨j,hunit⟩ := mem_iUnion.mp hunit
  change gridCoordinate j ((h n)⁻¹ • z) = (k:ℝ) at hunit
  rw [map_smul,smul_eq_mul] at hunit
  have hk := congrArg (fun r : ℝ => h n * r) hunit
  rw [← mul_assoc,mul_inv_cancel₀ (hh n).ne',one_mul] at hk
  exact hz (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨j,hk⟩⟩⟩)

end RepulsiveCoulomb
