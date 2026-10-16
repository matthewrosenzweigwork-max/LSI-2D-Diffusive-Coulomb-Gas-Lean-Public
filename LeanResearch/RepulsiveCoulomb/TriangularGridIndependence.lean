module

public import LeanResearch.RepulsiveCoulomb.TriangularGridConvexGeometry
public import Mathlib.LinearAlgebra.AffineSpace.Independent

@[expose] public section

/-! Actual affine independence of the regular physical grid triangles. -/
noncomputable section
namespace RepulsiveCoulomb

theorem gridLowerVertices_affineIndependent (b : ℤ × ℤ) :
    AffineIndependent ℝ (gridLowerVertices b) := by
  have hbase : AffineIndependent ℝ ![(0 : ℂ), 1, 1 + Complex.I] := by
    apply affineIndependent_of_ne_of_mem_of_mem_of_notMem
      (s := Complex.imCLM.toLinearMap.ker.toAffineSubspace) (by norm_num : (0 : ℂ) ≠ 1)
    · change (0 : ℂ).im = 0
      rfl
    · change (1 : ℂ).im = 0
      rfl
    · change (1 + Complex.I).im ≠ 0
      norm_num
  have ht := (affineIndependent_vadd (k := ℝ) (p := ![(0 : ℂ), 1, 1 + Complex.I])
    (v := complexLatticePoint b)).mpr hbase
  convert ht using 1
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [gridLowerVertices, complexLatticePoint, vadd_eq_add] <;> ring

theorem gridUpperVertices_affineIndependent (b : ℤ × ℤ) :
    AffineIndependent ℝ (gridUpperVertices b) := by
  have hne : (0 : ℂ) ≠ 1 + Complex.I := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hbase : AffineIndependent ℝ ![(0 : ℂ), 1 + Complex.I, Complex.I] := by
    apply affineIndependent_of_ne_of_mem_of_mem_of_notMem
      (s := (Complex.reCLM.toLinearMap - Complex.imCLM.toLinearMap).ker.toAffineSubspace) hne
    · change (0 : ℂ).re - (0 : ℂ).im = 0
      norm_num
    · change (1 + Complex.I).re - (1 + Complex.I).im = 0
      norm_num
    · change Complex.I.re - Complex.I.im ≠ 0
      norm_num
  have ht := (affineIndependent_vadd (k := ℝ) (p := ![(0 : ℂ), 1 + Complex.I, Complex.I])
    (v := complexLatticePoint b)).mpr hbase
  convert ht using 1
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [gridUpperVertices, complexLatticePoint, vadd_eq_add] <;> ring

end RepulsiveCoulomb
