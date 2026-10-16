import LeanResearch.RepulsiveCoulomb.TriangularInterpolantDerivative

/-! Exact translation covariance of the finite grid construction. -/
noncomputable section
namespace RepulsiveCoulomb

def gridTranslateCoefficients (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) : (ℤ × ℤ) →₀ ℝ :=
  Finsupp.equivMapDomain (Equiv.subRight b) v

theorem gridTranslateCoefficients_apply (v : (ℤ × ℤ) →₀ ℝ) (b p : ℤ × ℤ) :
    gridTranslateCoefficients v b p = v (p + b) := rfl

theorem triangularGridInterpolant_translate (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (z : ℂ) :
    triangularGridInterpolant (gridTranslateCoefficients v b) z =
      triangularGridInterpolant v (z + complexLatticePoint b) := by
  change (Finsupp.equivMapDomain (Equiv.subRight b) v).sum
      (fun p c => c * triangularGridHat (z - complexLatticePoint p)) =
    v.sum (fun p c => c * triangularGridHat (z + complexLatticePoint b - complexLatticePoint p))
  rw [Finsupp.sum_equivMapDomain]
  apply Finsupp.sum_congr
  intro p _
  congr 2
  change z - complexLatticePoint (p - b) = z + complexLatticePoint b - complexLatticePoint p
  rw [complexLatticePoint_sub]
  abel

theorem triangularGridInterpolant_cell_translate (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ) (z : ℂ) :
    triangularGridInterpolant v z =
      triangularGridInterpolant (gridTranslateCoefficients v b) (z - complexLatticePoint b) := by
  rw [triangularGridInterpolant_translate, sub_add_cancel]

theorem triangularGridInterpolant_lower_translated (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ)
    {z : ℂ} (hy0 : 0 ≤ (z - complexLatticePoint b).im)
    (hyx : (z - complexLatticePoint b).im ≤ (z - complexLatticePoint b).re)
    (hx1 : (z - complexLatticePoint b).re ≤ 1) :
    triangularGridInterpolant v z =
      v b * (1 - (z - complexLatticePoint b).re) +
      v (b + (1, 0)) * ((z - complexLatticePoint b).re - (z - complexLatticePoint b).im) +
      v (b + (1, 1)) * (z - complexLatticePoint b).im := by
  rw [triangularGridInterpolant_cell_translate v b z,
    triangularGridInterpolant_lower_cell _ hy0 hyx hx1]
  simp only [gridTranslateCoefficients_apply, show ((0, 0) : ℤ × ℤ) = 0 from rfl,
    zero_add, add_zero, add_comm]

theorem triangularGridInterpolant_upper_translated (v : (ℤ × ℤ) →₀ ℝ) (b : ℤ × ℤ)
    {z : ℂ} (hx0 : 0 ≤ (z - complexLatticePoint b).re)
    (hxy : (z - complexLatticePoint b).re ≤ (z - complexLatticePoint b).im)
    (hy1 : (z - complexLatticePoint b).im ≤ 1) :
    triangularGridInterpolant v z =
      v b * (1 - (z - complexLatticePoint b).im) +
      v (b + (1, 1)) * (z - complexLatticePoint b).re +
      v (b + (0, 1)) * ((z - complexLatticePoint b).im - (z - complexLatticePoint b).re) := by
  rw [triangularGridInterpolant_cell_translate v b z,
    triangularGridInterpolant_upper_cell _ hx0 hxy hy1]
  simp only [gridTranslateCoefficients_apply, show ((0, 0) : ℤ × ℤ) = 0 from rfl,
    zero_add, add_zero, add_comm]

end RepulsiveCoulomb
