import LeanResearch.RepulsiveCoulomb.PointFlatLinkOccupancy

/-! Isolated, uncompiled author draft. Global closed-sector adapter. Restrict
an actually distance-preserving closed-sector map to a unit sector disk, then
prove that no distant source point adds a hidden local image component. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def flatLinkSectorApex {β : ℝ} (hβ : 0 ≤ β) : closedEuclideanSector β :=
  ⟨0, by simp [closedEuclideanSector, hβ]⟩

def flatLinkSectorDiskInclusion {β L : ℝ} :
    flatLinkSectorDisk β L → closedEuclideanSector β := fun x ↦ ⟨x.1, x.2.1⟩

/-- Restriction loses no image point sufficiently close to the actual apex.
This is proved from ambient isometry, rather than from properness or an
unproved assertion that the local image is the correct component. -/
theorem pointFlatSector_local_range_iff_disk
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {β L ρ : ℝ}
    (hβ : 0 ≤ β) (hρL : ρ ≤ L)
    (f : closedEuclideanSector β → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {z : ℂ} (hz : (pointSmoothConformalEDist a y z (f (flatLinkSectorApex hβ))).toReal ≤ ρ) :
    z ∈ range f ↔ z ∈ range (f ∘ (flatLinkSectorDiskInclusion (L := L))) := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : ‖x.1‖ ≤ L := by
      rw [hd] at hz
      change dist x.1 (0 : ℂ) ≤ ρ at hz
      rw [dist_zero_right] at hz
      exact hz.trans hρL
    exact ⟨⟨x.1, x.2, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨flatLinkSectorDiskInclusion x, rfl⟩

/-- The requested closed-sector endpoint. Its hypotheses are only finite
nonnegative point exponents, 0 < beta <= pi, the actual source-sector map,
and literal all-pairs old-metric distance preservation. The chart, occupied
interval, source orientation, and exact physical width are all outputs. -/
theorem exists_pointFlatSector_link_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (f : closedEuclideanSector β → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    ∃ C : PointFlatLinkConeDisk a y (f (flatLinkSectorApex hβ.le)),
      ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
        ρ ≤ 1 ∧ ρ ≤ C.radius ∧ ∃ forward : Bool,
          (∀ s t : unitInterval,
            C.chart (f ⟨sectorPolar (ρ * s.1) (β * t.1),
              flatLink_polar_mem_sector hβ.le hβπ (mul_nonneg hρ.le s.2.1) t⟩) =
            sectorPolar (ρ * s.1) (flatLinkOrientedAngle forward
              (β / (coalescedPointExponent a y (f (flatLinkSectorApex hβ.le)) / 2 + 1)) t)) ∧
          (∀ z, (pointSmoothConformalEDist a y z (f (flatLinkSectorApex hβ.le))).toReal ≤ ρ →
            (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ 0
              (β / (coalescedPointExponent a y (f (flatLinkSectorApex hβ.le)) / 2 + 1)))) ∧
          (coalescedPointExponent a y (f (flatLinkSectorApex hβ.le)) / 2 + 1) *
            (β / (coalescedPointExponent a y (f (flatLinkSectorApex hβ.le)) / 2 + 1)) = β := by
  let g : flatLinkSectorDisk β 1 → ℂ := f ∘ flatLinkSectorDiskInclusion
  have hg (x z : flatLinkSectorDisk β 1) :
      (pointSmoothConformalEDist a y (g x) (g z)).toReal = dist x z :=
    hd (flatLinkSectorDiskInclusion x) (flatLinkSectorDiskInclusion z)
  obtain ⟨C, ρ, hρ, hρ1, hρC, forward, hpolar, hocc, hwidth⟩ :=
    exists_pointFlatLinkDisk_occupancy ha y hβ hβπ (by norm_num : (0 : ℝ) < 1) g hg
  refine ⟨C, ρ, hρ, hρ1, hρC, forward, hpolar, ?_, hwidth⟩
  intro z hz
  exact (pointFlatSector_local_range_iff_disk hβ.le hρ1 f hd hz).trans (hocc z hz)

/-- If the supplied embedding takes values in a retained region, the occupied
piece lies literally in that region. No intrinsic/ambient equality is assumed
by this elementary image-membership consequence. -/
theorem pointFlatLink_occupied_inverse_mem_retained
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {ρ lo hi : ℝ} (hρC : ρ ≤ C.radius)
    {S P : Set ℂ} (hSP : S ⊆ P)
    (hocc : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
      (z ∈ S ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo hi))
    {w : ℂ} (hw : w ∈ flatLinkOccupiedDisk ρ lo hi) : C.chart.symm w ∈ P := by
  have hnorm : ‖w‖ ≤ ρ := by
    obtain ⟨r, hr, θ, hθ, rfl⟩ := hw
    rw [sectorPolar_norm hr.1]
    exact hr.2
  exact hSP ((pointFlatLink_occupancy_inverse C hρC hocc hnorm).mpr hw)

end RepulsiveCoulomb
