import LeanResearch.RepulsiveCoulomb.TriangularGridConvexGeometry
import LeanResearch.RepulsiveCoulomb.AffineLevelEdge

/-! Actual affine formulas on each physical grid triangle and exact finite
representation of every nonzero interpolant level as triangle/line intersections. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridLowerAffine (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) : ℂ →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ ℂ (v b) + (v (b + (1, 0)) - v b) • gridRelativeRe b +
    (v (b + (1, 1)) - v (b + (1, 0))) • gridRelativeIm b

def gridUpperAffine (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) : ℂ →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ ℂ (v b) + (v (b + (1, 1)) - v (b + (0, 1))) • gridRelativeRe b +
    (v (b + (0, 1)) - v b) • gridRelativeIm b

theorem gridLowerAffine_apply (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (z : ℂ) :
    gridLowerAffine v b z = v b + (v (b + (1, 0)) - v b) * (z - complexLatticePoint b).re +
      (v (b + (1, 1)) - v (b + (1, 0))) * (z - complexLatticePoint b).im := rfl

theorem gridUpperAffine_apply (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (z : ℂ) :
    gridUpperAffine v b z = v b + (v (b + (1, 1)) - v (b + (0, 1))) * (z - complexLatticePoint b).re +
      (v (b + (0, 1)) - v b) * (z - complexLatticePoint b).im := rfl

theorem triangularGridInterpolant_eq_lowerAffine (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ)
    {z : ℂ} (hz : z ∈ gridLowerTriangle b) :
    triangularGridInterpolant v z = gridLowerAffine v b z := by
  rw [triangularGridInterpolant_lower_translated v b hz.1 hz.2.1 hz.2.2, gridLowerAffine_apply]
  ring

theorem triangularGridInterpolant_eq_upperAffine (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ)
    {z : ℂ} (hz : z ∈ gridUpperTriangle b) :
    triangularGridInterpolant v z = gridUpperAffine v b z := by
  rw [triangularGridInterpolant_upper_translated v b hz.1 hz.2.1 hz.2.2, gridUpperAffine_apply]
  ring

theorem gridLowerAffine_vertex_values (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (i : Fin 3) :
    gridLowerAffine v b (gridLowerVertices b i) = ![v b, v (b + (1, 0)), v (b + (1, 1))] i := by
  fin_cases i <;> simp [gridLowerAffine_apply, gridLowerVertices, complexLatticePoint] <;> ring

theorem gridUpperAffine_vertex_values (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (i : Fin 3) :
    gridUpperAffine v b (gridUpperVertices b i) = ![v b, v (b + (1, 1)), v (b + (0, 1))] i := by
  fin_cases i <;> simp [gridUpperAffine_apply, gridUpperVertices, complexLatticePoint] <;> ring

theorem triangularGridInterpolant_level_finite_affine_slices (v : (ℤ × ℤ) →₀ ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    (triangularGridInterpolant v) ⁻¹' {t} =
      ⋃ b ∈ gridActiveCells v,
        (gridLowerTriangle b ∩ (gridLowerAffine v b) ⁻¹' {t}) ∪
        (gridUpperTriangle b ∩ (gridUpperAffine v b) ⁻¹' {t}) := by
  ext z
  constructor
  · intro hz
    have hcell := triangularGridInterpolant_nonzero_level_finite_cells v ht hz
    obtain ⟨b, hb⟩ := mem_iUnion.mp hcell
    obtain ⟨hba, hbt⟩ := mem_iUnion.mp hb
    apply mem_iUnion.mpr
    refine ⟨b, mem_iUnion.mpr ⟨hba, ?_⟩⟩
    rcases hbt with hl | hu
    · exact Or.inl ⟨hl, (triangularGridInterpolant_eq_lowerAffine v b hl).symm.trans hz⟩
    · exact Or.inr ⟨hu, (triangularGridInterpolant_eq_upperAffine v b hu).symm.trans hz⟩
  · intro hz
    obtain ⟨b, hb⟩ := mem_iUnion.mp hz
    obtain ⟨_, hb⟩ := mem_iUnion.mp hb
    rcases hb with hl | hu
    · exact (triangularGridInterpolant_eq_lowerAffine v b hl.1).trans hl.2
    · exact (triangularGridInterpolant_eq_upperAffine v b hu.1).trans hu.2

theorem affineLevelEdgePoint_same_endpoint_values (f g : ℂ →ᵃ[ℝ] ℝ) (p q : ℂ) (t : ℝ)
    (hp : f p = g p) (hq : f q = g q) :
    affineLevelEdgePoint p q (f p) (f q) t = affineLevelEdgePoint p q (g p) (g q) t := by
  rw [hp, hq]

end RepulsiveCoulomb
