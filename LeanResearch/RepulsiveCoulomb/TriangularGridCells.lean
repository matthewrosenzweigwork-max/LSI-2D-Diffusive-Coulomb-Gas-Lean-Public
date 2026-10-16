module

public import LeanResearch.RepulsiveCoulomb.TriangularInterpolantTranslation
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! Actual diagonal-grid cells and finite active-cell coverage of the finite
nodal interpolant. A nonzero level is contained in finitely many actual triangles. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridLowerTriangle (b : ℤ × ℤ) : Set ℂ :=
  {z | 0 ≤ (z - complexLatticePoint b).im ∧
    (z - complexLatticePoint b).im ≤ (z - complexLatticePoint b).re ∧
    (z - complexLatticePoint b).re ≤ 1}

def gridUpperTriangle (b : ℤ × ℤ) : Set ℂ :=
  {z | 0 ≤ (z - complexLatticePoint b).re ∧
    (z - complexLatticePoint b).re ≤ (z - complexLatticePoint b).im ∧
    (z - complexLatticePoint b).im ≤ 1}

theorem exists_grid_triangle (z : ℂ) :
    ∃ b : ℤ × ℤ, z ∈ gridLowerTriangle b ∪ gridUpperTriangle b := by
  let b : ℤ × ℤ := (⌊z.re⌋, ⌊z.im⌋)
  have hx0 : 0 ≤ (z - complexLatticePoint b).re := by
    change 0 ≤ z.re - (⌊z.re⌋ : ℝ)
    exact sub_nonneg.mpr (Int.floor_le _)
  have hx1 : (z - complexLatticePoint b).re ≤ 1 := by
    change z.re - (⌊z.re⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one z.re]
  have hy0 : 0 ≤ (z - complexLatticePoint b).im := by
    change 0 ≤ z.im - (⌊z.im⌋ : ℝ)
    exact sub_nonneg.mpr (Int.floor_le _)
  have hy1 : (z - complexLatticePoint b).im ≤ 1 := by
    change z.im - (⌊z.im⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one z.im]
  refine ⟨b, ?_⟩
  rcases le_total (z - complexLatticePoint b).im (z - complexLatticePoint b).re with h | h
  · exact Or.inl ⟨hy0, h, hx1⟩
  · exact Or.inr ⟨hx0, h, hy1⟩

def gridActiveCells (v : (ℤ × ℤ) →₀ ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact v.support.biUnion (fun p => gridUnitCorners.image (fun q => p - q))

theorem grid_inactive_corner_zero (v : (ℤ × ℤ) →₀ ℝ) {b : ℤ × ℤ}
    (hb : b ∉ gridActiveCells v) {q : ℤ × ℤ} (hq : q ∈ gridUnitCorners) :
    v (b + q) = 0 := by
  classical
  by_contra h
  apply hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b + q, Finsupp.mem_support_iff.mpr h, ?_⟩
  exact Finset.mem_image.mpr ⟨q, hq, add_sub_cancel_right b q⟩

theorem triangularGridInterpolant_zero_inactive (v : (ℤ × ℤ) →₀ ℝ)
    {b : ℤ × ℤ} (hb : b ∉ gridActiveCells v) {z : ℂ}
    (hz : z ∈ gridLowerTriangle b ∪ gridUpperTriangle b) :
    triangularGridInterpolant v z = 0 := by
  have h0 := grid_inactive_corner_zero v hb (q := (0, 0)) (by simp [gridUnitCorners])
  have h1 := grid_inactive_corner_zero v hb (q := (1, 0)) (by simp [gridUnitCorners])
  have h2 := grid_inactive_corner_zero v hb (q := (1, 1)) (by simp [gridUnitCorners])
  have h3 := grid_inactive_corner_zero v hb (q := (0, 1)) (by simp [gridUnitCorners])
  have h0' : v b = 0 := by simpa only [show ((0, 0) : ℤ × ℤ) = 0 from rfl, add_zero] using h0
  rcases hz with hz | hz
  · rw [triangularGridInterpolant_lower_translated v b hz.1 hz.2.1 hz.2.2]
    simp only [h0', h1, h2, zero_mul, add_zero]
  · rw [triangularGridInterpolant_upper_translated v b hz.1 hz.2.1 hz.2.2]
    simp only [h0', h2, h3, zero_mul, add_zero]

theorem triangularGridInterpolant_support_finite_cells (v : (ℤ × ℤ) →₀ ℝ) :
    Function.support (triangularGridInterpolant v) ⊆
      ⋃ b ∈ gridActiveCells v, gridLowerTriangle b ∪ gridUpperTriangle b := by
  intro z hz
  obtain ⟨b, hb⟩ := exists_grid_triangle z
  have ha : b ∈ gridActiveCells v := by
    by_contra h
    exact hz (triangularGridInterpolant_zero_inactive v h hb)
  exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨ha, hb⟩⟩

theorem triangularGridInterpolant_nonzero_level_finite_cells (v : (ℤ × ℤ) →₀ ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    (triangularGridInterpolant v) ⁻¹' {t} ⊆
      ⋃ b ∈ gridActiveCells v, gridLowerTriangle b ∪ gridUpperTriangle b := by
  intro z hz
  apply triangularGridInterpolant_support_finite_cells v
  change triangularGridInterpolant v z ≠ 0
  rw [show triangularGridInterpolant v z = t from hz]
  exact ht

end RepulsiveCoulomb
