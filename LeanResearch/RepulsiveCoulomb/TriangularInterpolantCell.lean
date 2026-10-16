import LeanResearch.RepulsiveCoulomb.TriangularGridInterpolant

/-! Exact finite nodal-interpolant formulas on the reference cell. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

def gridUnitCorners : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (1, 1), (0, 1)}

theorem triangularGridHat_unit_cell_zero {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ 1)
    (p : ℤ × ℤ) (hp : p ∉ gridUnitCorners) :
    triangularGridHat (z - complexLatticePoint p) = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := triangularGridHat_unit_cell_indices hx0 hx1 hy0 hy1 p h
  apply hp
  rcases p with ⟨i, j⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp_all [gridUnitCorners]

theorem triangularGridInterpolant_cell_sum (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ 1) :
    triangularGridInterpolant v z =
      ∑ p ∈ gridUnitCorners, v p * triangularGridHat (z - complexLatticePoint p) := by
  classical
  let g : ℤ × ℤ → ℝ := fun p => v p * triangularGridHat (z - complexLatticePoint p)
  have h1 : (∑ p ∈ v.support, g p) = ∑ p ∈ v.support ∪ gridUnitCorners, g p := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p _ hp
    simp only [g, Finsupp.notMem_support_iff.mp hp, zero_mul]
  have h2 : (∑ p ∈ gridUnitCorners, g p) = ∑ p ∈ v.support ∪ gridUnitCorners, g p := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p _ hp
    simp only [g, triangularGridHat_unit_cell_zero hx0 hx1 hy0 hy1 p hp, mul_zero]
  exact h1.trans h2.symm

theorem triangularGridInterpolant_cell_expansion (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ 1) :
    triangularGridInterpolant v z = v (0, 0) * triangularGridHat z +
      v (1, 0) * triangularGridHat (z - 1) +
      v (1, 1) * triangularGridHat (z - (1 + Complex.I)) +
      v (0, 1) * triangularGridHat (z - Complex.I) := by
  rw [triangularGridInterpolant_cell_sum v hx0 hx1 hy0 hy1]
  have h0 : complexLatticePoint (0, 0) = 0 := by apply Complex.ext <;> norm_num [complexLatticePoint]
  have h1 : complexLatticePoint (1, 0) = 1 := by apply Complex.ext <;> norm_num [complexLatticePoint]
  have h2 : complexLatticePoint (1, 1) = 1 + Complex.I := by apply Complex.ext <;> norm_num [complexLatticePoint]
  have h3 : complexLatticePoint (0, 1) = Complex.I := by apply Complex.ext <;> norm_num [complexLatticePoint]
  simp only [gridUnitCorners, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, zero_ne_one, one_ne_zero, and_false, false_and, or_false, or_self,
    not_false_eq_true, Finset.sum_singleton, h0, h1, h2, h3, sub_zero]
  ring

theorem triangularGridInterpolant_lower_cell (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hy0 : 0 ≤ z.im) (hyx : z.im ≤ z.re) (hx1 : z.re ≤ 1) :
    triangularGridInterpolant v z = v (0, 0) * (1 - z.re) +
      v (1, 0) * (z.re - z.im) + v (1, 1) * z.im := by
  rw [triangularGridInterpolant_cell_expansion v (hy0.trans hyx) hx1 hy0 (hyx.trans hx1)]
  obtain ⟨h0, h1, h2, h3⟩ := triangularGridHat_lower_cell hy0 hyx hx1
  rw [h0, h1, h2, h3]
  ring

theorem triangularGridInterpolant_upper_cell (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hxy : z.re ≤ z.im) (hy1 : z.im ≤ 1) :
    triangularGridInterpolant v z = v (0, 0) * (1 - z.im) +
      v (1, 1) * z.re + v (0, 1) * (z.im - z.re) := by
  rw [triangularGridInterpolant_cell_expansion v hx0 (hxy.trans hy1) (hx0.trans hxy) hy1]
  obtain ⟨h0, h1, h2, h3⟩ := triangularGridHat_upper_cell hx0 hxy hy1
  rw [h0, h1, h2, h3]
  ring

end RepulsiveCoulomb
