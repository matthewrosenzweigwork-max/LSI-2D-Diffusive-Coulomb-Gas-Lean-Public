import LeanResearch.RepulsiveCoulomb.PointIncidentNormalizedCells
import LeanResearch.RepulsiveCoulomb.PointFlatLinkDirectedCommonChart

/-! SOURCE-ONLY, UNCOMPILED. Convert the constructed normalized endpoint
identities into exact full physical range membership in the same rotated
ambient cone chart used by the actual finite source cover. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace PointIncidentSectorSourcePatch
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ}

theorem rotated_normalized_polarAt (P : PointIncidentSectorSourcePatch S p)
    (C : PointFlatLinkConeDisk a y p) {ρ : ℝ} {hρP : ρ ≤ P.radius}
    {lo : ℝ} {forward : Bool} (hp : P.PolarAt C hρP lo forward) (origin : ℝ) :
    P.PolarAt (C.rotate (-origin)) hρP (normalizedIncidentLower origin lo) forward := by
  intro r hr t
  rw [PointFlatLinkConeDisk.rotate_apply, P.normalized_polarAt C hp origin r hr t,
    conePhase_mul_sectorPolar, conePhase_mul_sectorPolar]
  congr 1
  ring

/-- The whole original sector range, not only its truncated source patch,
has exactly the normalized occupied interval on the actual common ball. -/
theorem rotated_normalized_range_iff (P : PointIncidentSectorSourcePatch S p)
    (ha : ∀ j, 0 ≤ a j) (C : PointFlatLinkConeDisk a y p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ρ ≤ P.radius) (hρC : ρ ≤ C.radius)
    {lo : ℝ} {forward : Bool} (hp : P.PolarAt C hρP lo forward) (origin : ℝ)
    {z : ℂ} (hz : (pointSmoothConformalEDist a y z p).toReal ≤ ρ) :
    z ∈ range S.map ↔ (C.rotate (-origin)).chart z ∈
      flatLinkOccupiedDisk ρ (normalizedIncidentLower origin lo)
        (normalizedIncidentLower origin lo + P.angle / (coalescedPointExponent a y p / 2 + 1)) := by
  let D := C.rotate (-origin)
  let E := D.rewriteCenter P.map_center
  have hpn := P.rotated_normalized_polarAt C hp origin
  have hpunit : ∀ s t : unitInterval,
      E.chart (P.map (flatLinkSectorDiskPoint P.angle_pos.le P.angle_le_pi (ρ * s.1)
        ⟨mul_nonneg hρ.le s.2.1, (mul_le_of_le_one_right hρ.le s.2.2).trans hρP⟩ t)) =
        sectorPolar (ρ * s.1) (normalizedIncidentLower origin lo + flatLinkOrientedAngle forward
          (P.angle / (coalescedPointExponent a y
            (P.map (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le)) / 2 + 1)) t) := by
    intro s t
    simpa only [E, PointFlatLinkConeDisk.rewriteCenter_chart, P.map_center] using
      hpn (ρ * s.1) ⟨mul_nonneg hρ.le s.2.1, mul_le_of_le_one_right hρ.le s.2.2⟩ t
  have hocc := pointFlatLinkDisk_fixed_chart_occupancy_of_polar ha y P.angle_pos P.angle_le_pi
    P.radius_pos P.map P.metric E hρ hρP
    (by simpa only [E, D, PointFlatLinkConeDisk.rewriteCenter_radius, PointFlatLinkConeDisk.rotate] using hρC)
    (normalizedIncidentLower origin lo) forward hpunit z (by simpa only [P.map_center] using hz)
  have hocc' : z ∈ range P.map ↔ D.chart z ∈
      flatLinkOccupiedDisk ρ (normalizedIncidentLower origin lo)
        (normalizedIncidentLower origin lo + P.angle / (coalescedPointExponent a y p / 2 + 1)) := by
    simpa only [E, PointFlatLinkConeDisk.rewriteCenter_chart, P.map_center] using hocc
  exact (P.range_iff (hz.trans hρP)).trans hocc'

end PointIncidentSectorSourcePatch
end RepulsiveCoulomb
