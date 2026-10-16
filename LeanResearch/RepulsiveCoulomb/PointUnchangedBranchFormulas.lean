import LeanResearch.RepulsiveCoulomb.PointUnchangedSectorRangeCoordinates
import LeanResearch.RepulsiveCoulomb.DirectedSectorDiskRestriction

/-! SOURCE-ONLY, UNCOMPILED. Exact radial, inverse and center identities for
the unchanged complement branches. These are actual maps in the old cone
chart and do not treat an occupied passing piece as radial. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointUnchangedConeSectorMap_polar
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) (t : unitInterval) :
    C.chart (pointUnchangedConeSectorMap C lo (flatLinkSectorDiskPoint hβ hβπ r hr t)) =
      sectorPolar r (lo + (β / (coalescedPointExponent a y p / 2 + 1)) * t.1) := by
  rw [(pointUnchangedConeSectorMap_coordinate C lo hRC
    (flatLinkSectorDiskPoint hβ hβπ r hr t)).2]
  rw [flatLinkSectorDiskPoint_coe, sectorAngularMap_polar hr.1
    ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg hβ t.2.1),
      (mul_le_of_le_one_right hβ t.2.2).trans hβπ⟩, conePhase_mul_sectorPolar]
  congr 1
  simp only [div_eq_mul_inv]
  ring

theorem pointUnchangedConeSectorMap_center_distance
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) (hR : 0 ≤ R) (hRC : R ≤ C.radius)
    (w : flatLinkSectorDisk β R) :
    (pointSmoothConformalEDist a y (pointUnchangedConeSectorMap C lo w) p).toReal = ‖w.1‖ := by
  have h := pointUnchangedConeSectorMap_metric C lo hβπ hRC w
    (flatLinkSectorDiskApex hβ hR)
  rw [pointUnchangedConeSectorMap_center C lo hβ hR] at h
  exact h.trans (dist_zero_right w.1)

theorem pointUnchangedConeSectorRangeHomeomorph_apply
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (w : flatLinkSectorDisk β R) :
    (pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC w).1 =
      pointUnchangedConeSectorMap C lo w := rfl

theorem pointUnchangedConeSectorRangeHomeomorph_symm_apply
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (w : flatLinkSectorDisk β R) :
    (pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).symm
      ⟨pointUnchangedConeSectorMap C lo w, mem_range_self w⟩ = w :=
  (pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).symm_apply_apply w

theorem pointUnchangedConeSectorRangeHomeomorph_map_symm
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (z : range (pointUnchangedConeSectorMap (β := β) (R := R) C lo)) :
    pointUnchangedConeSectorMap C lo
      ((pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).symm z) = z.1 :=
  congrArg Subtype.val ((pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).apply_symm_apply z)

end RepulsiveCoulomb
