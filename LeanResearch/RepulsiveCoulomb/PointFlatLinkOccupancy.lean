import LeanResearch.RepulsiveCoulomb.PointFlatLinkNormalizedPolar

/-! Isolated, uncompiled author draft. Exact local image membership in a
constructed normalized cone chart. Physical width is the source angle, and a
passing halfdisk has physical width pi, including at an ambient cone point. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- This output concerns the image of the given actual embedding. The source
angle, not an assumed target occupation number, fixes the physical width. -/
theorem exists_pointFlatLinkDisk_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    ∃ C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)),
      ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρL : ρ ≤ L,
        ρ ≤ C.radius ∧ ∃ forward : Bool,
          (∀ s t : unitInterval,
            C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
              ⟨mul_nonneg hρ.le s.2.1,
                (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
            sectorPolar (ρ * s.1) (flatLinkOrientedAngle forward
              (β / (coalescedPointExponent a y
                (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t)) ∧
          (∀ z, (pointSmoothConformalEDist a y z
              (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
            (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ 0
              (β / (coalescedPointExponent a y
                (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)))) ∧
          (coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1) *
            (β / (coalescedPointExponent a y
              (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) = β := by
  obtain ⟨C, ρ, hρ, hρL, hρC, forward, hpolar⟩ :=
    exists_pointFlatLinkDisk_normalized_polar ha y hβ hβπ hL f hd
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by
    dsimp [k]
    linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β / k := div_pos hβ hk
  refine ⟨C, ρ, hρ, hρL, hρC, forward, hpolar, ?_, ?_⟩
  · intro z hz
    constructor
    · rintro ⟨x, rfl⟩
      have hx : ‖x.1‖ ≤ ρ := by
        rwa [pointFlatLinkDiskMap_dist_apex y hβ hL f hd] at hz
      obtain ⟨s, t, hst⟩ := flatLinkSectorDisk_representation hβ hβπ hρ hρL x hx
      rw [hst, hpolar]
      exact ⟨ρ * s.1, ⟨mul_nonneg hρ.le s.2.1,
        mul_le_of_le_one_right hρ.le s.2.2⟩,
        flatLinkOrientedAngle forward (β / k) t,
        flatLinkOrientedAngle_mem forward hw.le t, rfl⟩
    · rintro ⟨r, hr, θ, hθ, he⟩
      obtain ⟨t, ht⟩ := flatLinkOrientedAngle_surjective forward hw hθ
      let s : unitInterval := ⟨r / ρ, div_nonneg hr.1 hρ.le, (div_le_one hρ).mpr hr.2⟩
      have hrs : ρ * s.1 = r := mul_div_cancel₀ _ hρ.ne'
      let x := flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
        ⟨mul_nonneg hρ.le s.2.1,
          (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t
      have hxbound : (pointSmoothConformalEDist a y (f x) p).toReal ≤ C.radius := by
        rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
        change ‖sectorPolar (ρ * s.1) (β * t.1)‖ ≤ C.radius
        rw [sectorPolar_norm (mul_nonneg hρ.le s.2.1), hrs]
        exact hr.2.trans hρC
      refine ⟨x, C.chart.injOn (C.source hxbound) (C.source (hz.trans hρC)) ?_⟩
      change C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1) _ t)) = C.chart z
      rw [hpolar, hrs, ht]
      exact he.symm
  · change k * (β / k) = β
    exact mul_div_cancel₀ _ hk.ne'

/-- Coordinate-side membership, needed when gluing or subtracting literal
angular pieces. Onto-ness of the actual chart, not an abstract quotient, gives
the inverse-chart point and its correct old-metric radius. -/
theorem pointFlatLink_occupancy_inverse
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {ρ lo hi : ℝ} (hρC : ρ ≤ C.radius)
    {S : Set ℂ}
    (hocc : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
      (z ∈ S ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo hi))
    {w : ℂ} (hw : ‖w‖ ≤ ρ) :
    C.chart.symm w ∈ S ↔ w ∈ flatLinkOccupiedDisk ρ lo hi := by
  obtain ⟨z, hz, hzw⟩ := C.onto.surjOn (hw.trans hρC)
  have hn : (pointSmoothConformalEDist a y z p).toReal = ‖w‖ := by
    rw [← C.norm_chart hz, hzw]
  have hinv : C.chart.symm w = z := by rw [← hzw, C.chart.left_inv (C.source hz)]
  rw [hinv, hocc z (hn.le.trans hw), hzw]

/-- The passing-edge specialization. This is a real isometric halfdisk with
its center on the straight source edge. Its occupied physical angle is pi,
regardless of the ambient coalesced exponent. -/
theorem exists_pointFlatHalfDisk_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {L : ℝ} (hL : 0 < L)
    (f : flatLinkSectorDisk Real.pi L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    ∃ C : PointFlatLinkConeDisk a y
        (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ L ∧ ρ ≤ C.radius ∧
        (∀ z, (pointSmoothConformalEDist a y z
            (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal ≤ ρ →
          (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ 0
            (Real.pi / (coalescedPointExponent a y
              (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) / 2 + 1)))) ∧
        (coalescedPointExponent a y
          (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) / 2 + 1) *
          (Real.pi / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) / 2 + 1)) = Real.pi := by
  obtain ⟨C, ρ, hρ, hρL, hρC, forward, hpolar, hocc, hwidth⟩ :=
    exists_pointFlatLinkDisk_occupancy ha y Real.pi_pos le_rfl hL f hd
  exact ⟨C, ρ, hρ, hρL, hρC, hocc, hwidth⟩

end RepulsiveCoulomb
