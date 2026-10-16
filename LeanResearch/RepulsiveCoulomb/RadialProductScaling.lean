module

public import LeanResearch.RepulsiveCoulomb.RadialProductAverage

@[expose] public section

/-! The lower radial average at every positive scale, with no dependence on the
number, separation or multiplicities of the nonnegative radial locations. -/
noncomputable section
open Set MeasureTheory Real
open scoped BigOperators
namespace RepulsiveCoulomb

theorem radial_product_scaled {m : ℕ} (a d : Fin m → ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (∏ j, |r * t - d j| ^ a j) =
      (∏ j, r ^ a j) * ∏ j, |t - d j / r| ^ a j := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [show r * t - d j = r * (t - d j / r) by field_simp,
    abs_mul, abs_of_pos hr, Real.mul_rpow hr.le (abs_nonneg _)]

theorem radial_product_integral_lower {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j)
    {r : ℝ} (hr : 0 < r) :
    Real.exp (-4 * ∑ j, a j) * r * (∏ j, (r + d j) ^ a j) ≤
      ∫ t in (0 : ℝ)..r, ∏ j, |t - d j| ^ a j := by
  have hlow := radial_product_average_lower ha (fun j => d j / r)
    (fun j => div_nonneg (hd j) hr.le)
  have hscale : (∫ t in (0 : ℝ)..r, ∏ j, |t - d j| ^ a j) =
      r * (∏ j, r ^ a j) * ∫ t in (0 : ℝ)..1, ∏ j, |t - d j / r| ^ a j := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => ∏ j, |t - d j| ^ a j) (a := 0) (b := 1) r
    simp only [smul_eq_mul, mul_zero, mul_one] at h
    rw [← h]
    simp_rw [radial_product_scaled a d hr]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hprod : (∏ j, (r + d j) ^ a j) =
      (∏ j, r ^ a j) * ∏ j, (1 + d j / r) ^ a j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [show r + d j = r * (1 + d j / r) by field_simp,
      Real.mul_rpow hr.le (by have := hd j; positivity)]
  rw [hscale, hprod]
  have h := mul_le_mul_of_nonneg_left hlow
    (show 0 ≤ r * ∏ j, r ^ a j by positivity)
  nlinarith

end RepulsiveCoulomb
