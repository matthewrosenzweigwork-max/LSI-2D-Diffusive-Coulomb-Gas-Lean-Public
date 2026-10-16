module

public import LeanResearch.RepulsiveCoulomb.SectorVariation
public import LeanResearch.RepulsiveCoulomb.PointMetricLineNormalizedChart

@[expose] public section

/-! RECORDS-ONLY, UNCOMPILED DRAFT.

The inverse development of a Euclidean sector of width strictly below pi is
an actual isometry into the classical cone. The map is the accepted angular
contraction with factor `(alpha + 1)^{-1}`. Neither local convexity nor a
cone-chord certificate is an input. The zero exponent and apex cases are
included explicitly. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem complex_arg_div_of_sub_mem_Ioc {x z : ℂ} (hx : x ≠ 0) (hz : z ≠ 0)
    (harg : Complex.arg z - Complex.arg x ∈ Ioc (-Real.pi) Real.pi) :
    Complex.arg (z / x) = Complex.arg z - Complex.arg x := by
  rw [← Complex.arg_coe_angle_toReal_eq_arg (z / x),
    Complex.arg_div_coe_angle hz hx, ← Real.Angle.coe_sub]
  exact Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr harg

theorem sectorAngularMap_one (z : ℂ) : sectorAngularMap 1 z = z := by
  simpa only [sectorAngularMap, one_mul] using sectorPolar_norm_arg z

theorem sectorAngularMap_ne_zero {L : ℝ} {z : ℂ} (hz : z ≠ 0) :
    sectorAngularMap L z ≠ 0 := by
  intro he
  have hn := congrArg norm he
  rw [sectorAngularMap_norm, norm_zero] at hn
  exact hz (norm_eq_zero.mp hn)

/-- Exact inverse development, measured in the actual classical cone metric.
The source sector is permitted to have width zero. -/
theorem sectorAngularMap_classicalCone_dist {α β : ℝ} (hα : 0 ≤ α)
    (hβ : β < Real.pi) {x z : ℂ}
    (hx : x ∈ closedEuclideanSector β) (hz : z ∈ closedEuclideanSector β) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorAngularMap (α + 1)⁻¹ x) (sectorAngularMap (α + 1)⁻¹ z) = ‖x - z‖ := by
  rcases hα.eq_or_lt with he | hp
  · subst α
    norm_num only [zero_add, inv_one]
    rw [sectorAngularMap_one, sectorAngularMap_one, classicalCone_zero_dist, norm_sub_rev]
  · let L := (α + 1)⁻¹
    have ha1 : 0 < α + 1 := by linarith
    have hL0 : 0 < L := inv_pos.mpr ha1
    have hL1 : L ≤ 1 := by
      dsimp [L]
      exact (inv_le_one₀ ha1).mpr (by linarith)
    by_cases hx0 : x = 0
    · subst x
      rw [sectorAngularMap_zero]
      have hc := @dist_comm ℂ (classicalConeMetricSpace α hα).toPseudoMetricSpace
        0 (sectorAngularMap (α + 1)⁻¹ z)
      rw [hc, classicalCone_dist_apex, sectorAngularMap_norm, zero_sub, norm_neg]
    by_cases hz0 : z = 0
    · subst z
      rw [sectorAngularMap_zero, classicalCone_dist_apex, sectorAngularMap_norm, sub_zero]
    have hdif : |Complex.arg z - Complex.arg x| < Real.pi := by
      apply abs_lt.mpr
      constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
    have hscaled : |L * Complex.arg z - L * Complex.arg x| < Real.pi := by
      rw [← mul_sub, abs_mul, abs_of_pos hL0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hL1).trans_lt hdif
    have harg : Complex.arg
        (sectorAngularMap L z / sectorAngularMap L x) =
          L * Complex.arg z - L * Complex.arg x := by
      have hwin : Complex.arg (sectorAngularMap L z) -
          Complex.arg (sectorAngularMap L x) ∈ Ioc (-Real.pi) Real.pi := by
        rw [sectorAngularMap_arg hL0.le hL1 hβ.le hz,
          sectorAngularMap_arg hL0.le hL1 hβ.le hx]
        exact ⟨(abs_lt.mp hscaled).1, (abs_lt.mp hscaled).2.le⟩
      rw [complex_arg_div_of_sub_mem_Ioc
        (sectorAngularMap_ne_zero hx0) (sectorAngularMap_ne_zero hz0) hwin,
        sectorAngularMap_arg hL0.le hL1 hβ.le hz,
        sectorAngularMap_arg hL0.le hL1 hβ.le hx]
    have hcancel : (α + 1) * |L * Complex.arg z - L * Complex.arg x| =
        |Complex.arg z - Complex.arg x| := by
      rw [← mul_sub, abs_mul, abs_of_pos hL0, ← mul_assoc]
      dsimp [L]
      rw [mul_inv_cancel₀ ha1.ne', one_mul]
    have hs := sectorPolar_distance_sq ‖x‖ ‖z‖ (Complex.arg x) (Complex.arg z)
    rw [sectorPolar_norm_arg, sectorPolar_norm_arg] at hs
    change @dist ℂ (classicalConeMetricSpace α hα).toDist
      (sectorAngularMap L x) (sectorAngularMap L z) = _
    rw [classicalCone_distance_formula hp, sectorAngularMap_norm,
      sectorAngularMap_norm, harg, hcancel, min_eq_right hdif.le, Real.cos_abs,
      show Real.cos (Complex.arg z - Complex.arg x) =
        Real.cos (Complex.arg x - Complex.arg z) by rw [← Real.cos_neg]; congr 1; ring,
      ← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Adding an arbitrary base direction preserves the inverse-development
distance. No principal-argument assumption is imposed on the base direction. -/
theorem rotated_sectorAngularMap_classicalCone_dist {α β : ℝ} (hα : 0 ≤ α)
    (hβ : β < Real.pi) (θ : ℝ) {x z : ℂ}
    (hx : x ∈ closedEuclideanSector β) (hz : z ∈ closedEuclideanSector β) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist
      (conePhase θ * sectorAngularMap (α + 1)⁻¹ x)
      (conePhase θ * sectorAngularMap (α + 1)⁻¹ z) = ‖x - z‖ := by
  rw [classicalCone_rotation_dist hα (conePhase_norm θ)]
  exact sectorAngularMap_classicalCone_dist hα hβ hx hz

theorem conePhase_mul_sectorPolar (r θ φ : ℝ) :
    conePhase θ * sectorPolar r φ = sectorPolar r (θ + φ) := by
  simp only [sectorPolar, conePhase, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem sectorPolar_eq_pointRadialSectorPoint (r θ : ℝ) :
    sectorPolar r θ = pointRadialSectorPoint r θ := by
  simp only [sectorPolar, conePhase, pointRadialSectorPoint, Circle.coe_exp]

/-- The quotient identity is independent of principal-argument branches and
also valid for zero radii, with the field's usual zero-division convention. -/
theorem pointRadialSectorPoint_div (r s θ φ : ℝ) :
    pointRadialSectorPoint s φ / pointRadialSectorPoint r θ =
      ((s / r : ℝ) : ℂ) * (Circle.exp (φ - θ) : ℂ) := by
  simp only [pointRadialSectorPoint, Circle.exp_sub, Complex.ofReal_div]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv,
    Circle.coe_mul, Circle.coe_inv]
  ring

/-- The actual circular principal angle of two positive radial points is the
smaller directed angular width. The full closed interval `[0,2*pi]`, including
coincident boundary directions, is handled. -/
theorem pointRadialSectorPoint_principal_abs {r s θ φ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hθφ : θ ≤ φ)
    (hfull : φ - θ ≤ 2 * Real.pi) :
    |Complex.arg (pointRadialSectorPoint s φ / pointRadialSectorPoint r θ)| =
      min (φ - θ) (2 * Real.pi - (φ - θ)) := by
  rw [pointRadialSectorPoint_div, Complex.arg_real_mul _ (div_pos hs hr)]
  by_cases hzero : φ - θ = 0
  · simp only [hzero, Circle.exp_zero, Circle.coe_one, Complex.arg_one, abs_zero, sub_zero]
    exact (min_eq_left (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).symm
  by_cases htwo : φ - θ = 2 * Real.pi
  · simp only [htwo, Circle.exp_two_pi, Circle.coe_one, Complex.arg_one, abs_zero, sub_self]
    exact (min_eq_right (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).symm
  exact pointRadialSector_principal_abs
    (lt_of_le_of_ne (sub_nonneg.mpr hθφ) (Ne.symm hzero))
    (lt_of_le_of_ne hfull htwo)

/-- The coordinate image is in the literal directed radial interval, including
zero-radius points. This is an image theorem, not a convexity assumption. -/
theorem rotated_sectorAngularMap_radial_representative {α β R : ℝ}
    (hα : 0 ≤ α) (hβ : β < Real.pi) (θ : ℝ) {w : ℂ}
    (hw : w ∈ closedEuclideanSector β) (hR : ‖w‖ ≤ R) :
    ∃ r ∈ Icc (0 : ℝ) R, ∃ φ ∈ Icc θ (θ + (α + 1)⁻¹ * β),
      conePhase θ * sectorAngularMap (α + 1)⁻¹ w = pointRadialSectorPoint r φ := by
  have hL : 0 ≤ (α + 1)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨‖w‖, ⟨norm_nonneg _, hR⟩,
    θ + (α + 1)⁻¹ * Complex.arg w, ⟨?_, ?_⟩, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg hL hw.1)
  · have h := mul_le_mul_of_nonneg_left hw.2 hL
    linarith
  · rw [sectorAngularMap, conePhase_mul_sectorPolar, sectorPolar_eq_pointRadialSectorPoint]

end RepulsiveCoulomb
