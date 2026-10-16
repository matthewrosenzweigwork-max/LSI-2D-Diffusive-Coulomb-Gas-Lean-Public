import LeanResearch.RepulsiveCoulomb.EuclideanCenteredHalfDisk
import LeanResearch.RepulsiveCoulomb.PointFlatLinkCommonChart

/-! SOURCE-ONLY, UNCOMPILED. The actual passing-edge halfdisk is obtained by
restricting the original sector map to an explicit centered source halfdisk.
Its occupancy conclusion concerns the original full range, not a surrogate
piece whose equality with that range has been postulated. The physical old
angle is pi, even at an ambient cone point. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointCenteredHalfDiskMap {K : Set ℂ} {R : ℝ} (f : K → ℂ) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im)) :
    flatLinkSectorDisk Real.pi R → ℂ := f ∘ centeredHalfDiskInclusion e hK

theorem pointCenteredHalfDiskMap_dist {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {K : Set ℂ} {R : ℝ} (f : K → ℂ) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (x z : flatLinkSectorDisk Real.pi R) :
    (pointSmoothConformalEDist a y (pointCenteredHalfDiskMap f e hK x)
      (pointCenteredHalfDiskMap f e hK z)).toReal = dist x z := by
  rw [pointCenteredHalfDiskMap, Function.comp_apply, Function.comp_apply, hd]
  exact (centeredHalfDiskInclusion_isometry e hK).dist_eq x z

/-- The full sector and its centered patch have exactly the same range in
the indicated ambient metric ball. This is proved from the source isometry. -/
theorem pointCenteredHalfDiskMap_range_iff {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {K : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (f : K → ℂ) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {z : ℂ} (hz : (pointSmoothConformalEDist a y z
      (pointCenteredHalfDiskMap f e hK
        (flatLinkSectorDiskApex Real.pi_pos.le hR))).toReal ≤ R) :
    z ∈ range f ↔ z ∈ range (pointCenteredHalfDiskMap f e hK) := by
  constructor
  · rintro ⟨q, rfl⟩
    have hq : q ∈ range (centeredHalfDiskInclusion e hK) := by
      rw [centeredHalfDiskInclusion_range]
      change dist q.1 (e 0) ≤ R
      simpa only [pointCenteredHalfDiskMap, Function.comp_apply, hd,
        Subtype.dist_eq, centeredHalfDiskInclusion_center] using hz
    obtain ⟨w, hw⟩ := hq
    exact ⟨w, congrArg f hw⟩
  · rintro ⟨q, rfl⟩
    exact ⟨centeredHalfDiskInclusion e hK q, rfl⟩

/-- A passing edge occupies an actual old physical interval of width pi in
any prescribed ambient cone chart. Neither orientation nor interval origin
is assumed. The normalized chart width is pi divided by the cone factor. -/
theorem exists_pointPassingEdge_fixed_chart_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} {R : ℝ} (hR : 0 < R) (f : K → ℂ) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (pointCenteredHalfDiskMap f e hK
      (flatLinkSectorDiskApex Real.pi_pos.le hR.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∀ z,
      (pointSmoothConformalEDist a y z (pointCenteredHalfDiskMap f e hK
        (flatLinkSectorDiskApex Real.pi_pos.le hR.le))).toReal ≤ ρ →
      (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo
        (lo + Real.pi / (coalescedPointExponent a y
          (pointCenteredHalfDiskMap f e hK
            (flatLinkSectorDiskApex Real.pi_pos.le hR.le)) / 2 + 1))) := by
  obtain ⟨lo, hlo⟩ := exists_pointFlatLinkDisk_fixed_chart_occupancy ha y
    Real.pi_pos le_rfl hR (pointCenteredHalfDiskMap f e hK)
    (pointCenteredHalfDiskMap_dist f e hK hd) C hρ hρR hρC
  refine ⟨lo, fun z hz ↦ ?_⟩
  exact (pointCenteredHalfDiskMap_range_iff hR.le f e hK hd (hz.trans hρR)).trans
    (hlo z hz)

end RepulsiveCoulomb
