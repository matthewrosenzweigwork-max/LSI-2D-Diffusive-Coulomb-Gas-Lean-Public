import LeanResearch.RepulsiveCoulomb.ClassicalConeSectorIsometry

/-! The actual circular-cone through-apex criterion for two directions of a
retained interval. Both physical sides are checked; exponent zero is included. -/
noncomputable section
namespace RepulsiveCoulomb

theorem classicalCone_retained_through_apex {α r s θ φ : ℝ} (hα : 0 ≤ α)
    (hr : 0 < r) (hs : 0 < s) (hθφ : θ ≤ φ) (hfull : φ - θ ≤ 2 * Real.pi)
    (hsep : Real.pi ≤ (α + 1) * (φ - θ))
    (hcomp : Real.pi ≤ (α + 1) * (2 * Real.pi - (φ - θ))) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist
      (pointRadialSectorPoint r θ) (pointRadialSectorPoint s φ) = r + s := by
  rcases hα.eq_or_lt with hzero | hpos
  · subst α
    simp only [zero_add, one_mul] at hsep hcomp
    have hδ : θ - φ = -Real.pi := by linarith
    rw [classicalCone_zero_dist, ← sectorPolar_eq_pointRadialSectorPoint,
      ← sectorPolar_eq_pointRadialSectorPoint, norm_sub_rev]
    have hsq := sectorPolar_distance_sq r s θ φ
    rw [hδ, Real.cos_neg, Real.cos_pi] at hsq
    nlinarith [norm_nonneg (sectorPolar r θ - sectorPolar s φ)]
  · have hmin : Real.pi ≤ min ((α + 1) * (φ - θ))
        ((α + 1) * (2 * Real.pi - (φ - θ))) := le_min hsep hcomp
    rw [classicalCone_distance_formula hpos, pointRadialSectorPoint_norm hr.le,
      pointRadialSectorPoint_norm hs.le, pointRadialSectorPoint_principal_abs hr hs hθφ hfull,
      mul_min_of_nonneg _ _ (by linarith : 0 ≤ α + 1), min_eq_left hmin, Real.cos_pi]
    have heq : r ^ 2 + s ^ 2 - 2 * r * s * (-1) = (r + s) ^ 2 := by ring
    rw [heq, Real.sqrt_sq (add_pos hr hs).le]

end RepulsiveCoulomb
