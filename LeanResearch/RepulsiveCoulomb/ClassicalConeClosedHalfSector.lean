import LeanResearch.RepulsiveCoulomb.ClassicalConeSectorIsometry

/-! Source-only draft: the endpoint beta = pi is included. This supplies the
literal inverse development needed at intrinsically regular boundary points,
even when the ambient cone exponent is positive. No continuation is asserted. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Angular contraction into the actual classical cone is isometric on every
closed Euclidean sector of width at most pi, including the full halfplane. -/
theorem sectorAngularMap_classicalCone_dist_le_pi {α β : ℝ} (hα : 0 ≤ α)
    (hβ : β ≤ Real.pi) {x z : ℂ}
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
    have hLlt : L < 1 := by
      dsimp [L]
      exact (inv_lt_one₀ ha1).mpr (by linarith)
    by_cases hx0 : x = 0
    · subst x
      rw [sectorAngularMap_zero]
      have hc := @dist_comm ℂ (classicalConeMetricSpace α hα).toPseudoMetricSpace
        0 (sectorAngularMap (α + 1)⁻¹ z)
      rw [hc, classicalCone_dist_apex, sectorAngularMap_norm, zero_sub, norm_neg]
    by_cases hz0 : z = 0
    · subst z
      rw [sectorAngularMap_zero, classicalCone_dist_apex, sectorAngularMap_norm, sub_zero]
    have hdif : |Complex.arg z - Complex.arg x| ≤ Real.pi := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
    have hscaled : |L * Complex.arg z - L * Complex.arg x| < Real.pi := by
      rw [← mul_sub, abs_mul, abs_of_pos hL0]
      calc
        L * |Complex.arg z - Complex.arg x| ≤ L * Real.pi :=
          mul_le_mul_of_nonneg_left hdif hL0.le
        _ < Real.pi := by nlinarith [Real.pi_pos]
    have harg : Complex.arg (sectorAngularMap L z / sectorAngularMap L x) =
        L * Complex.arg z - L * Complex.arg x := by
      have hwin : Complex.arg (sectorAngularMap L z) -
          Complex.arg (sectorAngularMap L x) ∈ Ioc (-Real.pi) Real.pi := by
        rw [sectorAngularMap_arg hL0.le hLlt.le hβ hz,
          sectorAngularMap_arg hL0.le hLlt.le hβ hx]
        exact ⟨(abs_lt.mp hscaled).1, (abs_lt.mp hscaled).2.le⟩
      rw [complex_arg_div_of_sub_mem_Ioc
        (sectorAngularMap_ne_zero hx0) (sectorAngularMap_ne_zero hz0) hwin,
        sectorAngularMap_arg hL0.le hLlt.le hβ hz,
        sectorAngularMap_arg hL0.le hLlt.le hβ hx]
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
      sectorAngularMap_norm, harg, hcancel, min_eq_right hdif, Real.cos_abs,
      show Real.cos (Complex.arg z - Complex.arg x) =
        Real.cos (Complex.arg x - Complex.arg z) by rw [← Real.cos_neg]; congr 1; ring,
      ← hs, Real.sqrt_sq (norm_nonneg _)]

theorem rotated_sectorAngularMap_classicalCone_dist_le_pi {α β : ℝ} (hα : 0 ≤ α)
    (hβ : β ≤ Real.pi) (θ : ℝ) {x z : ℂ}
    (hx : x ∈ closedEuclideanSector β) (hz : z ∈ closedEuclideanSector β) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist
      (conePhase θ * sectorAngularMap (α + 1)⁻¹ x)
      (conePhase θ * sectorAngularMap (α + 1)⁻¹ z) = ‖x - z‖ := by
  rw [classicalCone_rotation_dist hα (conePhase_norm θ)]
  exact sectorAngularMap_classicalCone_dist_le_pi hα hβ hx hz

/-- Literal unwrapped target interval, valid also for the halfplane endpoint. -/
theorem rotated_sectorAngularMap_radial_representative_le_pi {α β R : ℝ}
    (hα : 0 ≤ α) (θ : ℝ) {w : ℂ}
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
