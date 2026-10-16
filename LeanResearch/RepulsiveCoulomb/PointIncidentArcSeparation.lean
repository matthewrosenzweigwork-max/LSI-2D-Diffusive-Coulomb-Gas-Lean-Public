import LeanResearch.RepulsiveCoulomb.PointIncidentSectorSourcePatch

/-! SOURCE-ONLY, UNCOMPILED. Derived directed common-chart models exclude
every closed ray of one sector from every open angular ray of another
disjoint sector. The conclusion compares actual polar points, so it includes
all periodic representatives and, in particular, every actual seam endpoint.
This is the geometric reason a seam origin need not split a passing piece. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def PointFlatLinkConeDisk.rewriteCenter
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ}
    (C : PointFlatLinkConeDisk a y p) (h : q = p) : PointFlatLinkConeDisk a y q :=
  h.symm ▸ C

@[simp] theorem PointFlatLinkConeDisk.rewriteCenter_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ}
    (C : PointFlatLinkConeDisk a y p) (h : q = p) :
    (C.rewriteCenter h).chart = C.chart := by cases h; rfl

@[simp] theorem PointFlatLinkConeDisk.rewriteCenter_radius
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ}
    (C : PointFlatLinkConeDisk a y p) (h : q = p) :
    (C.rewriteCenter h).radius = C.radius := by cases h; rfl

namespace PointIncidentSectorSourcePatch
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S E : PointActualAllocatedSector a y} {p : ℂ}

@[simp] theorem map_center (P : PointIncidentSectorSourcePatch S p) :
    P.map (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le) = p := P.center

def PolarAt (P : PointIncidentSectorSourcePatch S p)
    (C : PointFlatLinkConeDisk a y p) {ρ : ℝ} (hρP : ρ ≤ P.radius)
    (lo : ℝ) (forward : Bool) : Prop :=
  ∀ r (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval),
    C.chart (P.map (flatLinkSectorDiskPoint P.angle_pos.le P.angle_le_pi r
      ⟨hr.1, hr.2.trans hρP⟩ t)) =
      sectorPolar r (lo + flatLinkOrientedAngle forward
        (P.angle / (coalescedPointExponent a y p / 2 + 1)) t)

/-- The common-chart orientation is supplied by the actual old embedding. -/
theorem exists_polarAt (P : PointIncidentSectorSourcePatch S p)
    (ha : ∀ j, 0 ≤ a j) (C : PointFlatLinkConeDisk a y p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ρ ≤ P.radius) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∃ forward : Bool, P.PolarAt C hρP lo forward := by
  obtain ⟨lo, forward, hp⟩ := P.exists_directed_polar ha
    (C.rewriteCenter P.map_center) hρ hρP (by simpa using hρC)
  refine ⟨lo, forward, ?_⟩
  simpa only [PolarAt, PointFlatLinkConeDisk.rewriteCenter_chart, P.map_center] using hp

/-- No closed occupied direction of P equals an open occupied direction of
Q. Equality is tested at one common positive radius in the actual chart;
all angular representatives, including wrapping endpoints, are covered. -/
theorem closed_arc_disjoint_open_arc
    (P : PointIncidentSectorSourcePatch S p) (Q : PointIncidentSectorSourcePatch E p)
    (ha : ∀ j, 0 ≤ a j) (C : PointFlatLinkConeDisk a y p)
    (hdis : Disjoint (range S.map) E.openImage)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ρ ≤ P.radius) (hρQ : ρ ≤ Q.radius)
    (hρC : ρ ≤ C.radius)
    (loP loQ : ℝ) (forwardP forwardQ : Bool)
    (hP : P.PolarAt C hρP loP forwardP) (hQ : Q.PolarAt C hρQ loQ forwardQ)
    {θ φ : ℝ}
    (hθ : θ ∈ Icc loP (loP + P.angle / (coalescedPointExponent a y p / 2 + 1)))
    (hφ : φ ∈ Ioo loQ (loQ + Q.angle / (coalescedPointExponent a y p / 2 + 1))) :
    sectorPolar (ρ / 2) θ ≠ sectorPolar (ρ / 2) φ := by
  intro heq
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hwP : 0 < P.angle / k := div_pos P.angle_pos hk
  obtain ⟨t, ht⟩ := flatLinkOrientedAngle_surjective forwardP hwP
    (show θ - loP ∈ Icc (0 : ℝ) (P.angle / k) from
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  have hr : ρ / 2 ∈ Ioo (0 : ℝ) ρ := ⟨half_pos hρ, half_lt_self hρ⟩
  let x := flatLinkSectorDiskPoint P.angle_pos.le P.angle_le_pi (ρ / 2)
    ⟨hr.1.le, hr.2.le.trans hρP⟩ t
  let z := P.map x
  have hz : (pointSmoothConformalEDist a y z p).toReal ≤ ρ := by
    rw [← P.map_center]
    change (pointSmoothConformalEDist a y (P.map x)
      (P.map (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le))).toReal ≤ ρ
    rw [P.metric]
    change dist (sectorPolar (ρ / 2) (P.angle * t.1)) 0 ≤ ρ
    rw [dist_zero_right, sectorPolar_norm hr.1.le]
    exact hr.2.le
  have hzchart : C.chart z = sectorPolar (ρ / 2) φ := by
    have hh := hP (ρ / 2) ⟨hr.1.le, hr.2.le⟩ t
    have hθeq : loP + flatLinkOrientedAngle forwardP (P.angle / k) t = θ := by
      linarith [ht]
    rw [hθeq] at hh
    exact hh.trans heq
  let CQ := C.rewriteCenter Q.map_center
  have hCQ : CQ.chart = C.chart := C.rewriteCenter_chart Q.map_center
  have hQ' : ∀ r (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval),
      CQ.chart (Q.map (flatLinkSectorDiskPoint Q.angle_pos.le Q.angle_le_pi r
        ⟨hr.1, hr.2.trans hρQ⟩ t)) =
        sectorPolar r (loQ + flatLinkOrientedAngle forwardQ
          (Q.angle / (coalescedPointExponent a y
            (Q.map (flatLinkSectorDiskApex Q.angle_pos.le Q.radius_pos.le)) / 2 + 1)) t) := by
    simpa only [PolarAt, hCQ, Q.map_center] using hQ
  obtain ⟨w, hwz, hwi, hwim, hwR⟩ := pointFlatLinkDisk_open_arc_lift ha y
    Q.angle_pos Q.angle_le_pi Q.radius_pos Q.map Q.metric CQ hρ hρQ
    (by simpa only [CQ, PointFlatLinkConeDisk.rewriteCenter_radius] using hρC)
    loQ forwardQ hQ' (by simpa only [Q.map_center] using hz) hr
    (by simpa only [Q.map_center] using hφ) (by simpa only [hCQ] using hzchart)
  have hzS : z ∈ range S.map := ⟨P.sourceMap x, rfl⟩
  have hzE : z ∈ E.openImage := hwz ▸ Q.mem_openImage w hwi hwim (hwR.trans_le hρQ)
  exact Set.disjoint_left.mp hdis hzS hzE

end PointIncidentSectorSourcePatch
end RepulsiveCoulomb
