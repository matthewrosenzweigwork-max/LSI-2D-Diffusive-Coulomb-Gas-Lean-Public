module

public import LeanResearch.RepulsiveCoulomb.PointConeSmallAngle

@[expose] public section

/-! The classical all-pairs cosine formula for the constructed positive-exponent
cone metric. Circular angular separation uses the principal argument of z/x. -/
noncomputable section
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConeSectorMap_re (α : ℝ) (z : ℂ) :
    (pointConeSectorMap α z).re = coneRadialPotential α z * Real.cos ((α + 1) * Complex.arg z) := by
  simp only [pointConeSectorMap, coneRadialPotential, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.cpow_ofReal_re]
  rw [mul_comm (Complex.arg z) (α + 1)]
  ring

theorem pointConeSectorMap_im (α : ℝ) (z : ℂ) :
    (pointConeSectorMap α z).im = coneRadialPotential α z * Real.sin ((α + 1) * Complex.arg z) := by
  simp only [pointConeSectorMap, coneRadialPotential, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, Complex.cpow_ofReal_im]
  rw [mul_comm (Complex.arg z) (α + 1)]
  ring

theorem pointConeSectorMap_of_arg_zero (α : ℝ) {x : ℂ} (hx : Complex.arg x = 0) :
    pointConeSectorMap α x = (coneRadialPotential α x : ℂ) := by
  apply Complex.ext
  · simp [pointConeSectorMap_re, hx]
  · simp [pointConeSectorMap_im, hx]

theorem pointConeSectorMap_norm_radial {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    ‖pointConeSectorMap α z‖ = coneRadialPotential α z := by
  simpa [coneRadialPotential, div_eq_mul_inv, mul_comm] using pointConeSectorMap_norm hα z

theorem complex_norm_sub_real_sq (v : ℂ) (r : ℝ) :
    ‖v - (r : ℂ)‖ ^ 2 = ‖v‖ ^ 2 + r ^ 2 - 2 * r * v.re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

theorem standardCone_cosine_formula_normalized {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hx : Complex.arg x = 0) :
    (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z).toReal ^ 2 =
      coneRadialPotential α x ^ 2 + coneRadialPotential α z ^ 2 -
        2 * coneRadialPotential α x * coneRadialPotential α z *
          Real.cos (min Real.pi |(α + 1) * Complex.arg z|) := by
  by_cases hangle : |(α + 1) * Complex.arg z| < Real.pi
  · rw [min_eq_right hangle.le, Real.cos_abs, standardCone_distance_small_angle hα hx hangle,
      ENNReal.toReal_ofReal (norm_nonneg _), pointConeSectorMap_of_arg_zero α hx,
      complex_norm_sub_real_sq, pointConeSectorMap_norm_radial hα.le, pointConeSectorMap_re]
    ring
  · rw [min_eq_left (le_of_not_gt hangle), Real.cos_pi,
      standardCone_distance_large_angle hα hx (le_of_not_gt hangle),
      ENNReal.toReal_ofReal (add_nonneg (coneRadialPotential_nonneg hα.le x)
        (coneRadialPotential_nonneg hα.le z))]
    ring

theorem standardCone_cosine_formula {α : ℝ} (hα : 0 < α) (x z : ℂ) :
    (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z).toReal ^ 2 =
      coneRadialPotential α x ^ 2 + coneRadialPotential α z ^ 2 -
        2 * coneRadialPotential α x * coneRadialPotential α z *
          Real.cos (min Real.pi ((α + 1) * |Complex.arg (z / x)|)) := by
  by_cases hx : x = 0
  · subst x
    have hr0 : coneRadialPotential α 0 = 0 := by
      simp [coneRadialPotential, Real.zero_rpow (show α + 1 ≠ 0 by linarith)]
    rw [hr0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, mul_zero, zero_mul, zero_mul, sub_zero,
      standardCone_distance_from_apex hα, ENNReal.toReal_ofReal (by positivity)]
    congr 1
    unfold coneRadialPotential
    ring
  · let c := conePhase (-Complex.arg x)
    have hcx : c * x = (‖x‖ : ℂ) := conePhase_neg_arg_mul x
    have hargx : Complex.arg (c * x) = 0 := by
      rw [hcx, Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
    have hcz : c * z = (‖x‖ : ℂ) * (z / x) := by
      rw [← hcx]
      field_simp
    have hargz : Complex.arg (c * z) = Complex.arg (z / x) := by
      rw [hcz, Complex.arg_real_mul _ (norm_pos_iff.mpr hx)]
    have h := standardCone_cosine_formula_normalized hα hargx (z := c * z)
    rw [standardCone_rotation_invariant (conePhase_norm _), hargz, abs_mul,
      abs_of_pos (by linarith : 0 < α + 1)] at h
    simpa only [coneRadialPotential, norm_mul, c, conePhase_norm, one_mul] using h

theorem standardCone_distance_formula {α : ℝ} (hα : 0 < α) (x z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal (Real.sqrt (coneRadialPotential α x ^ 2 + coneRadialPotential α z ^ 2 -
        2 * coneRadialPotential α x * coneRadialPotential α z *
          Real.cos (min Real.pi ((α + 1) * |Complex.arg (z / x)|)))) := by
  rw [← standardCone_cosine_formula hα x z, Real.sqrt_sq_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
  exact (pointSmoothConformalEDist_lt_top (by intro j; dsimp [standardConeExponents]; positivity)
    standardConeLocations x z).ne

end RepulsiveCoulomb
