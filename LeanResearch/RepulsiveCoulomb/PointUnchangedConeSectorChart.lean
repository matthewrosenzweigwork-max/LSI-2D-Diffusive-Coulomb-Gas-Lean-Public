import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk
import LeanResearch.RepulsiveCoulomb.ClassicalConeClosedHalfSector
import LeanResearch.RepulsiveCoulomb.PointFlatLinkRadialTrace
import LeanResearch.RepulsiveCoulomb.PointFlatLinkDirectedCommonChart
import LeanResearch.RepulsiveCoulomb.PointIncidentArcSeparation

/-! SOURCE-ONLY, UNCOMPILED. Actual unchanged complement-piece coordinates
inside the already constructed ambient cone chart. Every short physical
angular interval has an explicit old-metric isometric inverse chart. This
does not assume that the whole ambient cone is flat. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointFlatLinkConeDisk.inverse_chart_on_closedBall
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {w : ℂ} (hw : ‖w‖ ≤ C.radius) :
    (pointSmoothConformalEDist a y (C.chart.symm w) p).toReal ≤ C.radius ∧
      C.chart (C.chart.symm w) = w := by
  obtain ⟨z, hz, hzw⟩ := C.onto.surjOn hw
  have hinv : C.chart.symm w = z := by
    rw [← hzw, C.chart.left_inv (C.source hz)]
  rw [hinv]
  exact ⟨hz, hzw⟩

def pointUnchangedConeSectorMap
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ} :
    flatLinkSectorDisk β R → ℂ := fun x ↦
  C.chart.symm (conePhase lo * sectorAngularMap (coalescedPointExponent a y p / 2 + 1)⁻¹ x.1)

theorem pointUnchangedConeSectorMap_coordinate
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ} (hRC : R ≤ C.radius)
    (x : flatLinkSectorDisk β R) :
    (pointSmoothConformalEDist a y (pointUnchangedConeSectorMap C lo x) p).toReal ≤ C.radius ∧
      C.chart (pointUnchangedConeSectorMap C lo x) =
        conePhase lo * sectorAngularMap (coalescedPointExponent a y p / 2 + 1)⁻¹ x.1 := by
  apply C.inverse_chart_on_closedBall
  rw [norm_mul, conePhase_norm, one_mul, sectorAngularMap_norm]
  exact x.2.2.trans hRC

theorem pointUnchangedConeSectorMap_metric
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (x z : flatLinkSectorDisk β R) :
    (pointSmoothConformalEDist a y (pointUnchangedConeSectorMap C lo x)
      (pointUnchangedConeSectorMap C lo z)).toReal = dist x z := by
  obtain ⟨hxR, hcx⟩ := pointUnchangedConeSectorMap_coordinate C lo hRC x
  obtain ⟨hzR, hcz⟩ := pointUnchangedConeSectorMap_coordinate C lo hRC z
  rw [C.metric _ hxR _ hzR, hcx, hcz]
  exact (rotated_sectorAngularMap_classicalCone_dist_le_pi
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hβπ lo x.2.1 z.2.1).trans
    (dist_eq_norm x.1 z.1).symm

theorem pointUnchangedConeSectorMap_center
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) :
    pointUnchangedConeSectorMap C lo (flatLinkSectorDiskApex hβ hR) = p := by
  change C.chart.symm (conePhase lo * sectorAngularMap _ 0) = p
  rw [sectorAngularMap_zero, mul_zero, ← C.center]
  exact C.chart.left_inv C.center_mem

theorem pointUnchangedConeSectorMap_continuous
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) (hRC : R ≤ C.radius) :
    Continuous (pointUnchangedConeSectorMap (β := β) (R := R) C lo) :=
  continuous_pointFlatLinkDiskMap ha y (pointUnchangedConeSectorMap C lo)
    (pointUnchangedConeSectorMap_metric C lo hβπ hRC)

/-- The unchanged inverse covers the entire actual closed cone wedge at the
chosen radius, not merely a smaller unspecified neighborhood of its center. -/
theorem pointUnchangedConeSectorMap_full_range
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) (hRC : R ≤ C.radius) :
    ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R →
      (z ∈ range (pointUnchangedConeSectorMap (β := β) (R := R) C lo) ↔
        C.chart z ∈ flatLinkOccupiedDisk R lo
          (lo + β / (coalescedPointExponent a y p / 2 + 1))) := by
  let g : flatLinkSectorDisk β R → ℂ := pointUnchangedConeSectorMap C lo
  have hg : ∀ x z, (pointSmoothConformalEDist a y (g x) (g z)).toReal = dist x z :=
    pointUnchangedConeSectorMap_metric C lo hβπ hRC
  have hcenter : g (flatLinkSectorDiskApex hβ.le hR.le) = p :=
    pointUnchangedConeSectorMap_center C lo hβ.le hR.le
  let D := C.rewriteCenter hcenter
  have hpolar : ∀ s t : unitInterval,
      C.chart (g (flatLinkSectorDiskPoint hβ.le hβπ (R * s.1)
        ⟨mul_nonneg hR.le s.2.1, mul_le_of_le_one_right hR.le s.2.2⟩ t)) =
        sectorPolar (R * s.1) (lo + flatLinkOrientedAngle true
          (β / (coalescedPointExponent a y p / 2 + 1)) t) := by
    intro s t
    rw [(pointUnchangedConeSectorMap_coordinate C lo hRC
      (flatLinkSectorDiskPoint hβ.le hβπ (R * s.1)
        ⟨mul_nonneg hR.le s.2.1, mul_le_of_le_one_right hR.le s.2.2⟩ t)).2]
    change conePhase lo * sectorAngularMap _ (sectorPolar (R * s.1) (β * t.1)) = _
    rw [sectorAngularMap_polar (mul_nonneg hR.le s.2.1)
      ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg hβ.le t.2.1),
        (mul_le_of_le_one_right hβ.le t.2.2).trans hβπ⟩,
      conePhase_mul_sectorPolar]
    congr 2
    simp only [flatLinkOrientedAngle, ↓reduceIte, div_eq_mul_inv]
    ring
  have hocc := pointFlatLinkDisk_fixed_chart_occupancy_of_polar ha y hβ hβπ hR g hg D
    hR le_rfl (by simpa only [D, PointFlatLinkConeDisk.rewriteCenter_radius] using hRC)
    lo true (by
      simpa only [D, PointFlatLinkConeDisk.rewriteCenter_chart, hcenter] using hpolar)
  simpa only [D, PointFlatLinkConeDisk.rewriteCenter_chart, hcenter] using hocc

end RepulsiveCoulomb
