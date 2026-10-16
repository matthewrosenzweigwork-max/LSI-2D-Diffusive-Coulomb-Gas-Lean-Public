module

public import LeanResearch.RepulsiveCoulomb.TriangularGridLocalGeometry

@[expose] public section

/-! Every physical point belongs to the zero-, one-, or two-dimensional stratum
of the actual diagonal integer grid. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem grid_point_classification (z : ℂ) :
    z ∈ range complexLatticePoint ∨
      (∃ e : GridEdge, z ∈ openSegment ℝ (complexLatticePoint e.1)
        (complexLatticePoint (gridEdgeEnd e))) ∨
      ∃ i : GridTriangle, z ∈ gridOpenTriangle i := by
  let k : ℤ := ⌊z.re⌋
  let l : ℤ := ⌊z.im⌋
  let x := z.re - (k : ℝ)
  let y := z.im - (l : ℝ)
  have hx0 : 0 ≤ x := sub_nonneg.mpr (Int.floor_le _)
  have hy0 : 0 ≤ y := sub_nonneg.mpr (Int.floor_le _)
  have hx1 : x < 1 := Int.fract_lt_one _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hre : z.re = (k : ℝ) + x := by dsimp [x]; ring
  have him : z.im = (l : ℝ) + y := by dsimp [y]; ring
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · left
      refine ⟨(k, l), ?_⟩
      apply Complex.ext <;> simp [complexLatticePoint, hre, him, hx, hy]
    · right; left
      refine ⟨((k, l), 1), ?_⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨y, ⟨lt_of_le_of_ne hy0 (Ne.symm hy), hy1⟩, ?_⟩
      apply Complex.ext
      · rw [(gridEdge_lineMap_coordinates ((k, l), 1) y).1]
        simp [hre, hx]
      · rw [(gridEdge_lineMap_coordinates ((k, l), 1) y).2]
        simp [him]
  · by_cases hy : y = 0
    · right; left
      refine ⟨((k, l), 0), ?_⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨x, ⟨lt_of_le_of_ne hx0 (Ne.symm hx), hx1⟩, ?_⟩
      apply Complex.ext
      · rw [(gridEdge_lineMap_coordinates ((k, l), 0) x).1]
        simp [hre]
      · rw [(gridEdge_lineMap_coordinates ((k, l), 0) x).2]
        simp [him, hy]
    · by_cases hxy : x = y
      · right; left
        refine ⟨((k, l), 2), ?_⟩
        rw [openSegment_eq_image_lineMap]
        refine ⟨x, ⟨lt_of_le_of_ne hx0 (Ne.symm hx), hx1⟩, ?_⟩
        apply Complex.ext
        · rw [(gridEdge_lineMap_coordinates ((k, l), 2) x).1]
          simp [hre]
        · rw [(gridEdge_lineMap_coordinates ((k, l), 2) x).2]
          simp [him, hxy]
      · right; right
        rcases lt_or_gt_of_ne hxy with hxy | hyx
        · refine ⟨((k, l), true), ?_⟩
          exact ⟨lt_of_le_of_ne hx0 (Ne.symm hx), hxy, hy1⟩
        · refine ⟨((k, l), false), ?_⟩
          exact ⟨lt_of_le_of_ne hy0 (Ne.symm hy), hyx, hx1⟩

end RepulsiveCoulomb
