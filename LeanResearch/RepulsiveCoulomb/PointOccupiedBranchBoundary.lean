import LeanResearch.RepulsiveCoulomb.PointIncidentRotatedOccupancy
import LeanResearch.RepulsiveCoulomb.PointPairedSectorSurgeryCoordinates
import LeanResearch.RepulsiveCoulomb.DirectedSectorDiskPlacement

/-! SOURCE-ONLY, UNCOMPILED. Actual forward and inverse occupied-branch
boundary formulas in the same seam-normalized old chart and ordered target
placement. The old orientation is retained verbatim through the paired maps. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace PointPairedSectorSurgeryCoordinates
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ} {c : ℝ}

theorem forward_seam (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hrold : r ≤ B.old.radius) (hrnew : r ≤ B.new.radius)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    S.localForward ha hc hc1 B.new
      ⟨B.sourcePatch.map (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r
        ⟨hr, hrold⟩ t), mem_range_self _⟩ = sectorPolar r (B.new.angle * t.1) := by
  have heq : S.localInverse ha hc hc1 B.new
      (flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi r ⟨hr, hrnew⟩ t) =
      ⟨B.sourcePatch.map (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r
        ⟨hr, hrold⟩ t), mem_range_self _⟩ :=
    Subtype.ext (B.inverse_seam ha hc hc1 r hr hrold hrnew t ht)
  rw [← heq, S.localForward_localInverse ha hc hc1 B.new]
  rfl

theorem placed_forward_seam (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool)
    (r : ℝ) (hr : 0 ≤ r) (hrold : r ≤ B.old.radius) (hrnew : r ≤ B.new.radius)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    directedSectorPlacement newlo B.new.angle forward
      (S.localForward ha hc hc1 B.new
        ⟨B.sourcePatch.map (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r
          ⟨hr, hrold⟩ t), mem_range_self _⟩) =
      sectorPolar r (newlo + flatLinkOrientedAngle forward B.new.angle t) := by
  rw [B.forward_seam ha hc hc1 r hr hrold hrnew t ht,
    directedSectorPlacement_polar_unitInterval]

theorem inverse_seam_rotated_chart (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {ρ : ℝ} (hρP : ρ ≤ B.old.radius)
    {lo : ℝ} {forward : Bool} (hp : B.sourcePatch.PolarAt C hρP lo forward)
    (origin r : ℝ) (hr : r ∈ Icc (0 : ℝ) ρ) (hrnew : r ≤ B.new.radius)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    (C.rotate (-origin)).chart
      (S.localInverse ha hc hc1 B.new
        (flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi r ⟨hr.1, hrnew⟩ t)).1 =
      sectorPolar r (normalizedIncidentLower origin lo + flatLinkOrientedAngle forward
        (B.old.angle / (coalescedPointExponent a y p / 2 + 1)) t) := by
  rw [B.inverse_seam ha hc hc1 r hr.1 (hr.2.trans hρP) hrnew t ht]
  exact B.sourcePatch.rotated_normalized_polarAt C hp origin r hr t

end PointPairedSectorSurgeryCoordinates
end RepulsiveCoulomb
