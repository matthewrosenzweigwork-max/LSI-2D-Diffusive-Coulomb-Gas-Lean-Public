module

public import LeanResearch.RepulsiveCoulomb.TriangularGridCells
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-! Genuine geometric grid triangles: affine coordinates, convexity, and exact
convex-hull realization by the three physical complex lattice vertices. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def gridRelativeRe (b : ℤ × ℤ) : ℂ →ᵃ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.toAffineMap - AffineMap.const ℝ ℂ (complexLatticePoint b).re

def gridRelativeIm (b : ℤ × ℤ) : ℂ →ᵃ[ℝ] ℝ :=
  Complex.imCLM.toLinearMap.toAffineMap - AffineMap.const ℝ ℂ (complexLatticePoint b).im

theorem gridRelativeRe_apply (b : ℤ × ℤ) (z : ℂ) :
    gridRelativeRe b z = (z - complexLatticePoint b).re := rfl

theorem gridRelativeIm_apply (b : ℤ × ℤ) (z : ℂ) :
    gridRelativeIm b z = (z - complexLatticePoint b).im := rfl

theorem gridLowerTriangle_convex (b : ℤ × ℤ) : Convex ℝ (gridLowerTriangle b) := by
  have h := ((convex_Ici (0 : ℝ)).affine_preimage (gridRelativeIm b)).inter
    (((convex_Ici (0 : ℝ)).affine_preimage (gridRelativeRe b - gridRelativeIm b)).inter
      ((convex_Iic (1 : ℝ)).affine_preimage (gridRelativeRe b)))
  convert h using 1
  ext z
  simp only [gridLowerTriangle, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici, mem_Iic,
    AffineMap.coe_sub, Pi.sub_apply, gridRelativeRe_apply, gridRelativeIm_apply, sub_nonneg]

theorem gridUpperTriangle_convex (b : ℤ × ℤ) : Convex ℝ (gridUpperTriangle b) := by
  have h := ((convex_Ici (0 : ℝ)).affine_preimage (gridRelativeRe b)).inter
    (((convex_Ici (0 : ℝ)).affine_preimage (gridRelativeIm b - gridRelativeRe b)).inter
      ((convex_Iic (1 : ℝ)).affine_preimage (gridRelativeIm b)))
  convert h using 1
  ext z
  simp only [gridUpperTriangle, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici, mem_Iic,
    AffineMap.coe_sub, Pi.sub_apply, gridRelativeRe_apply, gridRelativeIm_apply, sub_nonneg]

def gridLowerVertices (b : ℤ × ℤ) : Fin 3 → ℂ :=
  ![complexLatticePoint b, complexLatticePoint (b + (1, 0)), complexLatticePoint (b + (1, 1))]

def gridUpperVertices (b : ℤ × ℤ) : Fin 3 → ℂ :=
  ![complexLatticePoint b, complexLatticePoint (b + (1, 1)), complexLatticePoint (b + (0, 1))]

theorem gridLowerTriangle_eq_convexHull (b : ℤ × ℤ) :
    gridLowerTriangle b = convexHull ℝ (range (gridLowerVertices b)) := by
  apply Set.Subset.antisymm
  · intro z hz
    let r := (z - complexLatticePoint b).re
    let s := (z - complexLatticePoint b).im
    let w : Fin 3 → ℝ := ![1 - r, r - s, s]
    apply mem_convexHull_of_exists_fintype w (gridLowerVertices b)
    · intro i
      fin_cases i <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · exact sub_nonneg.mpr hz.2.2
      · exact sub_nonneg.mpr hz.2.1
      · exact hz.1
    · simp [w, Fin.sum_univ_succ]
    · exact fun i => mem_range_self i
    · apply Complex.ext <;>
        simp [w, r, s, gridLowerVertices, complexLatticePoint, Fin.sum_univ_succ,
          Complex.smul_re, Complex.smul_im] <;> ring
  · apply convexHull_min _ (gridLowerTriangle_convex b)
    rintro z ⟨i, rfl⟩
    fin_cases i <;> norm_num [gridLowerVertices, gridLowerTriangle, complexLatticePoint, add_comm]

theorem gridUpperTriangle_eq_convexHull (b : ℤ × ℤ) :
    gridUpperTriangle b = convexHull ℝ (range (gridUpperVertices b)) := by
  apply Set.Subset.antisymm
  · intro z hz
    let r := (z - complexLatticePoint b).re
    let s := (z - complexLatticePoint b).im
    let w : Fin 3 → ℝ := ![1 - s, r, s - r]
    apply mem_convexHull_of_exists_fintype w (gridUpperVertices b)
    · intro i
      fin_cases i <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · exact sub_nonneg.mpr hz.2.2
      · exact hz.1
      · exact sub_nonneg.mpr hz.2.1
    · simp [w, Fin.sum_univ_succ]
    · exact fun i => mem_range_self i
    · apply Complex.ext <;>
        simp [w, r, s, gridUpperVertices, complexLatticePoint, Fin.sum_univ_succ,
          Complex.smul_re, Complex.smul_im] <;> ring
  · apply convexHull_min _ (gridUpperTriangle_convex b)
    rintro z ⟨i, rfl⟩
    fin_cases i <;> norm_num [gridUpperVertices, gridUpperTriangle, complexLatticePoint, add_comm]

end RepulsiveCoulomb
