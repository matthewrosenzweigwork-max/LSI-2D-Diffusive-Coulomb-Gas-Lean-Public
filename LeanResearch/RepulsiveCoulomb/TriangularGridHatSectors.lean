module

public import LeanResearch.RepulsiveCoulomb.TriangularGridHat

@[expose] public section

/-! Exact affine-sector formulas for the explicit regular-grid nodal hat. -/
noncomputable section
namespace RepulsiveCoulomb

theorem triangularGridHat_sector_pos_lower {z : ℂ} (hy : 0 ≤ z.im) (hyx : z.im ≤ z.re) :
    triangularGridHat z = max 0 (1 - z.re) := by
  unfold triangularGridHat
  rw [abs_of_nonneg (hy.trans hyx), abs_of_nonneg hy, abs_of_nonneg (sub_nonneg.mpr hyx),
    max_eq_left (max_le hyx (sub_le_self _ hy))]

theorem triangularGridHat_sector_pos_upper {z : ℂ} (hx : 0 ≤ z.re) (hxy : z.re ≤ z.im) :
    triangularGridHat z = max 0 (1 - z.im) := by
  unfold triangularGridHat
  rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy), abs_of_nonpos (sub_nonpos.mpr hxy)]
  have h : -(z.re - z.im) ≤ z.im := by linarith
  rw [max_eq_left h, max_eq_right hxy]

theorem triangularGridHat_sector_neg_pos {z : ℂ} (hx : z.re ≤ 0) (hy : 0 ≤ z.im) :
    triangularGridHat z = max 0 (1 + z.re - z.im) := by
  unfold triangularGridHat
  rw [abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonpos (by linarith : z.re - z.im ≤ 0)]
  rw [max_eq_right (show z.im ≤ -(z.re - z.im) by linarith),
    max_eq_right (show -z.re ≤ -(z.re - z.im) by linarith)]
  congr 1
  ring

theorem triangularGridHat_sector_neg_lower {z : ℂ} (hx : z.re ≤ 0) (hyx : z.im ≤ z.re) :
    triangularGridHat z = max 0 (1 + z.im) := by
  unfold triangularGridHat
  rw [abs_of_nonpos hx, abs_of_nonpos (hyx.trans hx), abs_of_nonneg (sub_nonneg.mpr hyx)]
  rw [max_eq_left (show z.re - z.im ≤ -z.im by linarith),
    max_eq_right (show -z.re ≤ -z.im by linarith), sub_neg_eq_add]

theorem triangularGridHat_sector_neg_upper {z : ℂ} (hy : z.im ≤ 0) (hxy : z.re ≤ z.im) :
    triangularGridHat z = max 0 (1 + z.re) := by
  unfold triangularGridHat
  rw [abs_of_nonpos (hxy.trans hy), abs_of_nonpos hy, abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_eq_left (max_le (by linarith : -z.im ≤ -z.re)
    (by linarith : -(z.re - z.im) ≤ -z.re)), sub_neg_eq_add]

theorem triangularGridHat_sector_pos_neg {z : ℂ} (hx : 0 ≤ z.re) (hy : z.im ≤ 0) :
    triangularGridHat z = max 0 (1 - z.re + z.im) := by
  unfold triangularGridHat
  rw [abs_of_nonneg hx, abs_of_nonpos hy, abs_of_nonneg (by linarith : 0 ≤ z.re - z.im)]
  rw [max_eq_right (show -z.im ≤ z.re - z.im by linarith),
    max_eq_right (show z.re ≤ z.re - z.im by linarith)]
  congr 1
  ring

end RepulsiveCoulomb
