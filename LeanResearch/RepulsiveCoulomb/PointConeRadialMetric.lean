module

public import LeanResearch.RepulsiveCoulomb.PointConformalConeCoordinate
public import Mathlib.Analysis.InnerProductSpace.NormPow

@[expose] public section

/-! The radial scale of the model cone, using the actual smooth-path metric.
No metric-cone isometry is postulated. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def standardConeExponents (α : ℝ) : Fin 1 → ℝ := fun _ ↦ 2 * α
def standardConeLocations : Fin 1 → ℂ := fun _ ↦ 0

theorem standardCone_density (α : ℝ) (z : ℂ) :
    pointConformalDensity (standardConeExponents α) standardConeLocations z = ‖z‖ ^ α := by
  simp only [pointConformalDensity, rawPointWeight, standardConeExponents, standardConeLocations,
    Fin.prod_univ_one, sub_zero]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

def coneRadialPotential (α : ℝ) (z : ℂ) : ℝ := (α + 1)⁻¹ * ‖z‖ ^ (α + 1)

theorem coneRadialPotential_contDiff {α : ℝ} (hα : 0 < α) :
    ContDiff ℝ 1 (coneRadialPotential α) := by
  have h : ContDiff ℝ 1 (fun z : ℂ ↦ ‖z‖ ^ (α + 1)) := contDiff_norm_rpow (by linarith)
  exact contDiff_const.mul h

theorem coneRadialPotential_norm_fderiv {α : ℝ} (hα : 0 < α) (z : ℂ) :
    ‖fderiv ℝ (coneRadialPotential α) z‖ = ‖z‖ ^ α := by
  have hp : 1 < α + 1 := by linarith
  have he : α + 1 ≠ 0 := by linarith
  change ‖fderiv ℝ (fun z : ℂ ↦ (α + 1)⁻¹ * ‖z‖ ^ (α + 1)) z‖ = _
  rw [fderiv_const_mul (differentiable_norm_rpow hp z) (α + 1)⁻¹, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith)), norm_fderiv_norm_id_rpow z hp]
  rw [show α + 1 - 1 = α by ring]
  field_simp

theorem coneRadialPotential_nonneg {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    0 ≤ coneRadialPotential α z :=
  mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)

theorem standardCone_distance_radial_lower {α : ℝ} (hα : 0 < α) (z : ℂ) :
    ENNReal.ofReal (coneRadialPotential α z) ≤
      pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 z := by
  have hb (w : ℂ) : ‖fderiv ℝ (coneRadialPotential α) w‖ ≤
      1 * pointConformalDensity (standardConeExponents α) standardConeLocations w := by
    rw [coneRadialPotential_norm_fderiv hα, standardCone_density, one_mul]
  have h := pointConformal_metric_barrier (standardConeExponents α) standardConeLocations
    (coneRadialPotential_contDiff hα) zero_lt_one hb 0 z
  have h0 : coneRadialPotential α 0 = 0 := by
    simp [coneRadialPotential, Real.zero_rpow (show α + 1 ≠ 0 by linarith)]
  rw [h0, sub_zero, ENNReal.ofReal_one, one_mul, ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg (coneRadialPotential_nonneg hα.le z)] at h
  exact h

theorem lintegral_unit_rpow {α : ℝ} (hα : 0 ≤ α) :
    (∫⁻ t : ℝ in Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ α)) = ENNReal.ofReal ((α + 1)⁻¹) := by
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ α) (Icc (0 : ℝ) 1) :=
    (Real.continuous_rpow_const hα).continuousOn.integrableOn_compact isCompact_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun t : ℝ ↦ t ^ α) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Real.rpow_nonneg ht.1 _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have he : (∫ t : ℝ in Icc (0 : ℝ) 1, t ^ α) = ∫ t : ℝ in (0 : ℝ)..1, t ^ α := by
    rw [intervalIntegral.integral_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  rw [he, integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow (show α + 1 ≠ 0 by linarith)]

theorem standardCone_radial_path_length {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    pointConformalPathELength (standardConeExponents α) standardConeLocations
      (fun t : ℝ ↦ t • z) 0 1 = ENNReal.ofReal (coneRadialPotential α z) := by
  have hd (t : ℝ) : deriv (fun t : ℝ ↦ t • z) t = z := by
    simpa using ((hasDerivAt_id t).smul_const z).deriv
  calc
    _ = ∫⁻ t : ℝ in Icc (0 : ℝ) 1,
        ENNReal.ofReal (‖z‖ ^ α * ‖z‖) * ENNReal.ofReal (t ^ α) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      change ENNReal.ofReal (pointConformalDensity (standardConeExponents α) standardConeLocations (t • z)) *
        ENNReal.ofReal ‖deriv (fun t : ℝ ↦ t • z) t‖ =
        ENNReal.ofReal (‖z‖ ^ α * ‖z‖) * ENNReal.ofReal (t ^ α)
      rw [hd, standardCone_density, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        Real.mul_rpow ht.1 (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg ht.1 _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
      ring
    _ = ENNReal.ofReal (‖z‖ ^ α * ‖z‖) * ENNReal.ofReal ((α + 1)⁻¹) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_unit_rpow hα]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
      congr 1
      rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : α + 1 ≠ 0)]
      unfold coneRadialPotential
      ring

theorem standardCone_distance_radial_upper {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 z ≤
      ENNReal.ofReal (coneRadialPotential α z) := by
  have h := pointSmoothConformalEDist_le_path (standardConeExponents α) standardConeLocations
    (γ := fun t : ℝ ↦ t • z) (s := 0) (t := 1) (by fun_prop) zero_le_one
  rw [standardCone_radial_path_length hα] at h
  simpa using h

/-- The actual distance to the apex fixes the radial coordinate of the cone. -/
theorem standardCone_distance_from_apex {α : ℝ} (hα : 0 < α) (z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 z =
      ENNReal.ofReal (‖z‖ ^ (α + 1) / (α + 1)) := by
  have h := le_antisymm (standardCone_distance_radial_upper hα.le z)
    (standardCone_distance_radial_lower hα z)
  simpa [coneRadialPotential, div_eq_mul_inv, mul_comm] using h

theorem standardCone_circle_length (α : ℝ) {R : ℝ} (hR : 0 < R) :
    pointConformalPathELength (standardConeExponents α) standardConeLocations
      (circleMap 0 R) 0 (2 * Real.pi) = ENNReal.ofReal (2 * Real.pi * R ^ (α + 1)) := by
  unfold pointConformalPathELength
  simp_rw [standardCone_density, deriv_circleMap, norm_mul, norm_circleMap_zero,
    Complex.norm_I, mul_one, abs_of_pos hR]
  rw [lintegral_const]
  simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _) hR.le)]
  congr 1
  rw [← Real.rpow_add_one hR.ne']
  ring

/-- Circumference divided by the actual apex distance gives the cone angle. -/
theorem standardCone_circle_length_eq_angle_mul_radius {α : ℝ} (hα : 0 < α)
    {R : ℝ} (hR : 0 < R) :
    pointConformalPathELength (standardConeExponents α) standardConeLocations
      (circleMap 0 R) 0 (2 * Real.pi) = ENNReal.ofReal (2 * Real.pi * (α + 1)) *
        pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 (R : ℂ) := by
  rw [standardCone_circle_length α hR, standardCone_distance_from_apex hα,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi * (α + 1))]
  congr 1
  have hn : α + 1 ≠ 0 := by linarith
  field_simp

theorem standardCone_zero_distance (x z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents 0) standardConeLocations x z =
      ENNReal.ofReal ‖z - x‖ := by
  apply le_antisymm
  · let γ : ℝ → ℂ := fun t ↦ x + t • (z - x)
    have hd (t : ℝ) : deriv γ t = z - x := by
      have h : HasDerivAt γ (z - x) t := by
        simpa [γ] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
      exact h.deriv
    have h := pointSmoothConformalEDist_le_path (standardConeExponents 0) standardConeLocations
      (γ := γ) (s := 0) (t := 1) (by fun_prop) zero_le_one
    have hlen : pointConformalPathELength (standardConeExponents 0) standardConeLocations γ 0 1 =
        ENNReal.ofReal ‖z - x‖ := by
      unfold pointConformalPathELength
      simp [standardCone_density, hd]
    rw [hlen] at h
    simpa [γ] using h
  · by_contra hbad
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist
      (standardConeExponents 0) standardConeLocations (lt_of_not_ge hbad)
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ.contDiffOn zero_le_one
    rw [h0, h1] at h
    have he : pointConformalPathELength (standardConeExponents 0) standardConeLocations γ 0 1 =
        ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv γ t‖ₑ := by
      simp [pointConformalPathELength, standardCone_density]
    rw [he, ofReal_norm] at hlen
    exact (not_lt_of_ge h) hlen

theorem standardCone_distance_from_apex_nonneg {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 z =
      ENNReal.ofReal (‖z‖ ^ (α + 1) / (α + 1)) := by
  rcases eq_or_lt_of_le hα with h | h
  · subst α
    simpa using standardCone_zero_distance 0 z
  · exact standardCone_distance_from_apex h z

end RepulsiveCoulomb
