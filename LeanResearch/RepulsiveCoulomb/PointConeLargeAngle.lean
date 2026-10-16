module

public import LeanResearch.RepulsiveCoulomb.PointConeBarrierSmooth

@[expose] public section

/-! Exact classical-cone distance in the regime where the developed angular
separation is at least pi. The minimizing distance is the sum of apex radii. -/
noncomputable section
open scoped ENNReal
namespace RepulsiveCoulomb

theorem coneAngularBarrier_eq_radial_of_arg_zero (α : ℝ) {x : ℂ} (hx : Complex.arg x = 0) :
    coneAngularBarrier α x = coneRadialPotential α x := by
  unfold coneAngularBarrier coneRadialPotential
  simp [hx, coneClippedCos, Real.pi_pos.le, div_eq_mul_inv, mul_comm]

theorem standardCone_distance_large_angle {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hx : Complex.arg x = 0) (hz : Real.pi ≤ |(α + 1) * Complex.arg z|) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal (coneRadialPotential α x + coneRadialPotential α z) := by
  have hRx := coneRadialPotential_nonneg hα.le x
  have hRz := coneRadialPotential_nonneg hα.le z
  apply le_antisymm
  · have h := pointSmoothConformalEDist_triangle (standardConeExponents α) standardConeLocations x 0 z
    have h0x := standardCone_distance_from_apex hα x
    have h0z := standardCone_distance_from_apex hα z
    rw [pointSmoothConformalEDist_comm (standardConeExponents α) standardConeLocations x 0, h0x, h0z] at h
    rw [ENNReal.ofReal_add hRx hRz]
    simpa [coneRadialPotential, div_eq_mul_inv, mul_comm] using h
  · have h := coneAngularBarrier_metric_lower hα x z
    rw [coneAngularBarrier_eq_radial_of_arg_zero α hx, coneAngularBarrier_eq_neg_radial hz,
      abs_of_nonpos (by linarith : -coneRadialPotential α z - coneRadialPotential α x ≤ 0)] at h
    convert h using 1
    congr 1
    ring

theorem standardCone_distance_large_angle_rotated {α : ℝ} (hα : 0 < α) {c x z : ℂ}
    (hc : ‖c‖ = 1) (hx : Complex.arg (c * x) = 0)
    (hz : Real.pi ≤ |(α + 1) * Complex.arg (c * z)|) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal (coneRadialPotential α x + coneRadialPotential α z) := by
  have h := standardCone_distance_large_angle hα hx hz
  rw [standardCone_rotation_invariant hc] at h
  simpa only [coneRadialPotential, norm_mul, hc, one_mul] using h

end RepulsiveCoulomb
