module

public import LeanResearch.RepulsiveCoulomb.TriangularGridHatSectors

@[expose] public section

/-! Exact barycentric hat values on both triangles of the reference unit cell. -/
noncomputable section
namespace RepulsiveCoulomb

theorem triangularGridHat_lower_cell {z : ℂ} (hy : 0 ≤ z.im)
    (hyx : z.im ≤ z.re) (hx : z.re ≤ 1) :
    triangularGridHat z = 1 - z.re ∧
    triangularGridHat (z - 1) = z.re - z.im ∧
    triangularGridHat (z - (1 + Complex.I)) = z.im ∧
    triangularGridHat (z - Complex.I) = 0 := by
  have hx0 : 0 ≤ z.re := hy.trans hyx
  have hy1 : z.im ≤ 1 := hyx.trans hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [triangularGridHat_sector_pos_lower hy hyx, max_eq_right (by linarith)]
  · rw [triangularGridHat_sector_neg_pos
      (show (z - 1).re ≤ 0 by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (show 0 ≤ (z - 1).im by simpa using hy)]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    rw [max_eq_right (by linarith)]
    ring
  · rw [triangularGridHat_sector_neg_lower
      (show (z - (1 + Complex.I)).re ≤ 0 by simp; linarith)
      (show (z - (1 + Complex.I)).im ≤ (z - (1 + Complex.I)).re by simp; linarith)]
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.I_im, zero_add]
    rw [max_eq_right (by linarith)]
    ring
  · rw [triangularGridHat_sector_pos_neg
      (show 0 ≤ (z - Complex.I).re by simpa using hx0)
      (show (z - Complex.I).im ≤ 0 by simp; linarith)]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
    rw [max_eq_left (by linarith)]

theorem triangularGridHat_upper_cell {z : ℂ} (hx : 0 ≤ z.re)
    (hxy : z.re ≤ z.im) (hy : z.im ≤ 1) :
    triangularGridHat z = 1 - z.im ∧
    triangularGridHat (z - 1) = 0 ∧
    triangularGridHat (z - (1 + Complex.I)) = z.re ∧
    triangularGridHat (z - Complex.I) = z.im - z.re := by
  have hy0 : 0 ≤ z.im := hx.trans hxy
  have hx1 : z.re ≤ 1 := hxy.trans hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [triangularGridHat_sector_pos_upper hx hxy, max_eq_right (by linarith)]
  · rw [triangularGridHat_sector_neg_pos
      (show (z - 1).re ≤ 0 by simp; linarith)
      (show 0 ≤ (z - 1).im by simpa using hy0)]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    rw [max_eq_left (by linarith)]
  · rw [triangularGridHat_sector_neg_upper
      (show (z - (1 + Complex.I)).im ≤ 0 by simp; linarith)
      (show (z - (1 + Complex.I)).re ≤ (z - (1 + Complex.I)).im by simp; linarith)]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.I_re, add_zero]
    rw [max_eq_right (by linarith)]
    ring
  · rw [triangularGridHat_sector_pos_neg
      (show 0 ≤ (z - Complex.I).re by simpa using hx)
      (show (z - Complex.I).im ≤ 0 by simp; linarith)]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
    rw [max_eq_right (by linarith)]
    ring

theorem triangularGridHat_cell_partition {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ 1) :
    triangularGridHat z + triangularGridHat (z - 1) +
      triangularGridHat (z - (1 + Complex.I)) + triangularGridHat (z - Complex.I) = 1 := by
  rcases le_total z.im z.re with h | h
  · obtain ⟨h0, h1, h2, h3⟩ := triangularGridHat_lower_cell hy0 h hx1
    rw [h0, h1, h2, h3]
    ring
  · obtain ⟨h0, h1, h2, h3⟩ := triangularGridHat_upper_cell hx0 h hy1
    rw [h0, h1, h2, h3]
    ring

end RepulsiveCoulomb
