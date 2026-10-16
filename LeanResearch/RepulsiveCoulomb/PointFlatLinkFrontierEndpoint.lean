import LeanResearch.RepulsiveCoulomb.PointFlatLinkOldIntervalAlignment
import LeanResearch.RepulsiveCoulomb.PointRetainedFrontierEndpoint

/-! NEW SOURCE-ONLY, UNCOMPILED. The actual old-frontier condition identifies
one of the two complete old interval endpoints. Both orientations remain
explicit. `PointRetainedFrontierEndpoint` is a separate new audited draft, not
silently assumed to have been accepted. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- An actual non-apex old-frontier point has one of the two endpoint-ray
coordinates at its actual metric radius. -/
theorem PointRetainedConeNeighborhood.frontier_chart_endpoint
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hzP : z ∈ P) (hz : z ∈ frontier P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρC : ρ < C.radius)
    (hd : (pointSmoothConformalEDist a y z p).toReal = ρ) :
    C.chart z = sectorPolar ρ C.lo ∨ C.chart z = sectorPolar ρ C.hi := by
  have hzC : (pointSmoothConformalEDist a y z p).toReal < C.radius := hd.trans_lt hρC
  obtain ⟨r,hr,θ,hθ,he⟩ := (C.retained z hzC.le).mp hzP
  have hn := congrArg norm he
  rw [pointRadialSectorPoint_norm hr.1] at hn
  have hrρ : r = ρ := hn.symm.trans ((C.retainedWidth_chart_norm hzC.le).trans hd)
  rw [hrρ] at he
  rcases C.frontier_radial_coordinate_endpoint hz hzC hρ hθ he with hlo | hhi
  · left
    rw [hlo] at he
    exact he.trans (sectorPolar_eq_pointRadialSectorPoint _ _).symm
  · right
    rw [hhi] at he
    exact he.trans (sectorPolar_eq_pointRadialSectorPoint _ _).symm

/-- The first source edge lies in the actual old boundary; its placement in
one old endpoint is a theorem, not an angular-alignment premise. -/
theorem pointFlatLinkDisk_first_edge_endpoint
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0) ∈ frontier P) :
    C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) = sectorPolar ρ C.lo ∨
    C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) = sectorPolar ρ C.hi := by
  apply C.frontier_chart_endpoint (hfP _) hfront hρ hρC
  rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
  exact sectorPolar_norm hρ.le _

end RepulsiveCoulomb
