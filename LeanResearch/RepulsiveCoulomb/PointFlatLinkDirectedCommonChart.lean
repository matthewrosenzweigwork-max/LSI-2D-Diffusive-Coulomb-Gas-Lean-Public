module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkCommonChart

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Retain the actual orientation furnished by the
flat-arc rigidity theorem, together with its exact full occupied interval.
The Boolean is constructed from the map; it is not supplied as a same-order
or orientation-preservation certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The same explicit polar formula determines the full occupied range. -/
theorem pointFlatLinkDisk_fixed_chart_occupancy_of_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (lo : ℝ) (forward : Bool)
    (hpolar : ∀ s t : unitInterval,
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
        ⟨mul_nonneg hρ.le s.2.1,
          (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
        sectorPolar (ρ * s.1) (lo + flatLinkOrientedAngle forward
          (β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t)) :
    ∀ z, (pointSmoothConformalEDist a y z
        (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
      (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo
        (lo + β / (coalescedPointExponent a y
          (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1))) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by
    dsimp [k]
    linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β / k := div_pos hβ hk
  intro z hz
  constructor
  · rintro ⟨x, rfl⟩
    have hx : ‖x.1‖ ≤ ρ := by
      rwa [pointFlatLinkDiskMap_dist_apex y hβ hL f hd] at hz
    obtain ⟨s, t, hst⟩ := flatLinkSectorDisk_representation hβ hβπ hρ hρL x hx
    rw [hst, hpolar]
    refine ⟨ρ * s.1, ⟨mul_nonneg hρ.le s.2.1,
      mul_le_of_le_one_right hρ.le s.2.2⟩,
      lo + flatLinkOrientedAngle forward (β / k) t, ?_, rfl⟩
    have ht := flatLinkOrientedAngle_mem forward hw.le t
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rintro ⟨r, hr, θ, hθ, he⟩
    obtain ⟨t, ht⟩ := flatLinkOrientedAngle_surjective forward hw
      (show θ - lo ∈ Icc 0 (β / k) from ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
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
    have hangle : lo + flatLinkOrientedAngle forward (β / k) t = θ := by linarith [ht]
    rw [hpolar, hrs, hangle]
    exact he.symm


/-- Combined directed-polar and full-range output, all derived from an actual
isometric sector or halfdisk map in a fixed full cone chart. -/
theorem exists_pointFlatLinkDisk_fixed_chart_directed_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∃ forward : Bool,
      (∀ s t : unitInterval,
        C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
          ⟨mul_nonneg hρ.le s.2.1,
            (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
          sectorPolar (ρ * s.1) (lo + flatLinkOrientedAngle forward
            (β / (coalescedPointExponent a y
              (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t)) ∧
      (∀ z, (pointSmoothConformalEDist a y z
          (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
        (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo
          (lo + β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)))) := by
  obtain ⟨lo, forward, hp⟩ := exists_pointFlatLinkDisk_fixed_chart_polar
    ha y hβ hβπ hL f hd C hρ hρL hρC
  exact ⟨lo, forward, hp, pointFlatLinkDisk_fixed_chart_occupancy_of_polar
    ha y hβ hβπ hL f hd C hρ hρL hρC lo forward hp⟩

end RepulsiveCoulomb
