import LeanResearch.RepulsiveCoulomb.PointFlatLinkFrontierEndpoint

/-! NEW SOURCE-ONLY, UNCOMPILED. If the two source edges of an actual flat
sector meet the two old boundary germs, the sector fills the entire old region
locally. The old angle is DERIVED, not a premise. Both orientations are handled.
Only actual boundary membership of two positive-radius source edge points is
needed; the directed full interval lift and isometry rule out endpoint collapse. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem flatBoundary_interval_radius_iff {r R lo hi : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    z ∈ pointClosedRadialInterval R lo hi ↔ z ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s,hs,θ,hθ,he⟩
    refine ⟨s,⟨hs.1,?_⟩,θ,hθ,he⟩
    rw [he,pointRadialSectorPoint_norm hs.1] at hz
    exact hz
  · rintro ⟨s,hs,θ,hθ,he⟩
    exact ⟨s,⟨hs.1,hs.2.trans hrR⟩,θ,hθ,he⟩

/-- This proves the full old width and literal local image equality from the
actual map and its old-boundary contact. No link-width equality, residual chart,
or curvature update is supplied. -/
theorem pointFlatLinkDisk_fills_old_boundary_interval
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront0 : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0) ∈ frontier P)
    (hfront1 : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 1) ∈ frontier P) :
    C.flatPhysicalWidth = β ∧
      ∀ z, (pointSmoothConformalEDist a y z
          (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
        (z ∈ range f ↔ z ∈ P) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β/k := div_pos hβ hk
  let q := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩
  have hqdist (t : unitInterval) :
      (pointSmoothConformalEDist a y (f (q t)) p).toReal = ρ := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hρ.le _
  have hqR (t : unitInterval) :
      (pointSmoothConformalEDist a y (f (q t)) p).toReal < C.radius :=
    (hqdist t).trans_lt hρC
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C hρ hρL hρC hfront0 with hlow | hupp
  · obtain ⟨hwidth,hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
      f hd hfP C hadm hρ hρL hρC.le hlow
    have hedge : C.chart (f (q 1)) = pointRadialSectorPoint ρ (C.lo+β/k) := by
      have he := hpolar 1 1
      simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one,
        sectorPolar_eq_pointRadialSectorPoint] using he
    have hcoord : C.lo+β/k ∈ Icc C.lo C.hi := ⟨by linarith,hwidth⟩
    have hend := C.frontier_radial_coordinate_endpoint hfront1 (hqR 1) hρ hcoord hedge
    have he : C.lo+β/k = C.hi := hend.resolve_left (by linarith)
    have hspan : C.hi-C.lo = β/k := by linarith
    have hfull : C.flatPhysicalWidth = β := by
      change k*(C.hi-C.lo) = β
      rw [hspan]
      exact mul_div_cancel₀ _ hk.ne'
    obtain ⟨_,hocc⟩ := pointFlatLinkDisk_old_lower_occupancy ha y hβ hβπ hL
      f hd hfP C hadm hρ hρL hρC.le hlow
    refine ⟨hfull,?_⟩
    intro z hz
    have hn : ‖C.chart z‖ ≤ ρ := (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho := hocc z hz
    rw [he] at ho
    exact ho.trans ((flatBoundary_interval_radius_iff hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)
  · obtain ⟨hwidth,hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
      f hd hfP C hadm hρ hρL hρC.le hupp
    have hedge : C.chart (f (q 1)) = pointRadialSectorPoint ρ (C.hi-β/k) := by
      have he := hpolar 1 1
      simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one,
        sectorPolar_eq_pointRadialSectorPoint] using he
    have hcoord : C.hi-β/k ∈ Icc C.lo C.hi := ⟨hwidth,by linarith⟩
    have hend := C.frontier_radial_coordinate_endpoint hfront1 (hqR 1) hρ hcoord hedge
    have he : C.hi-β/k = C.lo := hend.resolve_right (by linarith)
    have hspan : C.hi-C.lo = β/k := by linarith
    have hfull : C.flatPhysicalWidth = β := by
      change k*(C.hi-C.lo) = β
      rw [hspan]
      exact mul_div_cancel₀ _ hk.ne'
    obtain ⟨_,hocc⟩ := pointFlatLinkDisk_old_upper_occupancy ha y hβ hβπ hL
      f hd hfP C hadm hρ hρL hρC.le hupp
    refine ⟨hfull,?_⟩
    intro z hz
    have hn : ‖C.chart z‖ ≤ ρ := (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho := hocc z hz
    rw [he] at ho
    exact ho.trans ((flatBoundary_interval_radius_iff hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)

end RepulsiveCoulomb
