module

public import LeanResearch.RepulsiveCoulomb.ConeGeodesicAngle

@[expose] public section

/-! The two complementary sector angles at a minimizing passage through a cone
vertex are both at least pi. Their turns are nonpositive and sum to the actual
cone curvature. No global choice of interior side or Gauss–Bonnet is assumed. -/
noncomputable section
namespace RepulsiveCoulomb

def coneShortSectorAngle (α : ℝ) (u v : ℂ) : ℝ :=
  (α + 1) * |Complex.arg (v / u)|

def coneLongSectorAngle (α : ℝ) (u v : ℂ) : ℝ :=
  2 * Real.pi * (α + 1) - coneShortSectorAngle α u v

theorem coneShortSectorAngle_le_half_total {α : ℝ} (hα : 0 ≤ α) (u v : ℂ) :
    coneShortSectorAngle α u v ≤ Real.pi * (α + 1) := by
  dsimp [coneShortSectorAngle]
  nlinarith [mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi (v / u))
    (show 0 ≤ α + 1 by positivity)]

theorem coneShortSectorAngle_le_long {α : ℝ} (hα : 0 ≤ α) (u v : ℂ) :
    coneShortSectorAngle α u v ≤ coneLongSectorAngle α u v := by
  dsimp [coneLongSectorAngle]
  nlinarith [coneShortSectorAngle_le_half_total hα u v]

theorem cone_sector_turn_sum (α : ℝ) (u v : ℂ) :
    (Real.pi - coneShortSectorAngle α u v) + (Real.pi - coneLongSectorAngle α u v) =
      -(2 * Real.pi * α) := by
  dsimp [coneLongSectorAngle]
  ring

theorem cone_minimizing_sector_turns_nonpos {α : ℝ} (hα : 0 < α)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hmin : @dist ℂ (classicalConeMetricSpace α hα.le).toDist u v = ‖u‖ + ‖v‖) :
    Real.pi - coneShortSectorAngle α u v ≤ 0 ∧
      Real.pi - coneLongSectorAngle α u v ≤ 0 := by
  have hs := (classicalCone_apex_triangle_eq_iff hα hu hv).mp hmin
  change Real.pi ≤ coneShortSectorAngle α u v at hs
  exact ⟨sub_nonpos.mpr hs,
    sub_nonpos.mpr (hs.trans (coneShortSectorAngle_le_long hα.le u v))⟩

/-- The sum equals the already identified curvature atom -pi times the
coalesced exponent, with no separation or positive contribution from zero weights. -/
theorem point_cone_sector_turn_sum {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p u v : ℂ) :
    (Real.pi - coneShortSectorAngle (coalescedPointExponent a y p / 2) u v) +
      (Real.pi - coneLongSectorAngle (coalescedPointExponent a y p / 2) u v) =
      -(Real.pi * coalescedPointExponent a y p) := by
  rw [cone_sector_turn_sum]
  ring

end RepulsiveCoulomb
