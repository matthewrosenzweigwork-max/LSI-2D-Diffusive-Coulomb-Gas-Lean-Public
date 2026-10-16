import LeanResearch.RepulsiveCoulomb.PointFlatLinkDirectedCommonChart
import LeanResearch.RepulsiveCoulomb.EuclideanSectorBoundaryCases

/-! SOURCE-ONLY, UNCOMPILED. Open angular points lift to actual source
interior points. This is the geometric input needed to exclude another
sector's seam endpoint from an occupied open arc, using the already proved
closed-range/open-image disjointness. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem flatLinkOrientedAngle_strict_iff {width : ℝ} (hw : 0 < width)
    (forward : Bool) (t : unitInterval) :
    flatLinkOrientedAngle forward width t ∈ Ioo 0 width ↔ t.1 ∈ Ioo (0 : ℝ) 1 := by
  cases forward <;> simp only [flatLinkOrientedAngle, Bool.false_eq_true, ↓reduceIte,
    mem_Ioo] <;> constructor
  all_goals rintro ⟨h₁, h₂⟩; constructor <;> nlinarith

/-- The same derived polar formula written with an actual radius, rather
than a unit-interval rescaling. -/
theorem exists_pointFlatLinkDisk_fixed_chart_radial_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∃ forward : Bool, ∀ r (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval),
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ r ⟨hr.1, hr.2.trans hρL⟩ t)) =
        sectorPolar r (lo + flatLinkOrientedAngle forward
          (β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t) := by
  obtain ⟨lo, forward, hp⟩ := exists_pointFlatLinkDisk_fixed_chart_polar
    ha y hβ hβπ hL f hd C hρ hρL hρC
  refine ⟨lo, forward, fun r hr t ↦ ?_⟩
  let s : unitInterval := ⟨r / ρ, div_nonneg hr.1 hρ.le, (div_le_one hρ).mpr hr.2⟩
  have hrs : ρ * s.1 = r := mul_div_cancel₀ _ hρ.ne'
  simpa only [hrs] using hp s t

/-- In the fixed full cone chart, every strict occupied angular point at a
strictly smaller positive radius comes from the literal sector interior.
No interior-image equality is assumed. -/
theorem pointFlatLinkDisk_open_arc_lift
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (lo : ℝ) (forward : Bool)
    (hp : ∀ r (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval),
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ r ⟨hr.1, hr.2.trans hρL⟩ t)) =
        sectorPolar r (lo + flatLinkOrientedAngle forward
          (β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t))
    {z : ℂ} (hz : (pointSmoothConformalEDist a y z
      (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ)
    {r θ : ℝ} (hr : r ∈ Ioo (0 : ℝ) ρ)
    (hθ : θ ∈ Ioo lo (lo + β / (coalescedPointExponent a y
      (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)))
    (he : C.chart z = sectorPolar r θ) :
    ∃ x : flatLinkSectorDisk β L, f x = z ∧
      x.1 ∈ interior (closedEuclideanSector β) ∧ 0 < x.1.im ∧ ‖x.1‖ < ρ := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β / k := div_pos hβ hk
  obtain ⟨t, ht⟩ := flatLinkOrientedAngle_surjective forward hw
    (show θ - lo ∈ Icc (0 : ℝ) (β / k) from ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  have htstrict : t.1 ∈ Ioo (0 : ℝ) 1 :=
    (flatLinkOrientedAngle_strict_iff hw forward t).mp (by
      rw [ht]
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  let x := flatLinkSectorDiskPoint hβ.le hβπ r ⟨hr.1.le, hr.2.le.trans hρL⟩ t
  have hangle : β * t.1 ∈ Ioo (0 : ℝ) β :=
    ⟨mul_pos hβ htstrict.1, by nlinarith [htstrict.2]⟩
  have hxbound : (pointSmoothConformalEDist a y (f x) p).toReal ≤ C.radius := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar r (β * t.1)‖ ≤ C.radius
    rw [sectorPolar_norm hr.1.le]
    exact hr.2.le.trans hρC
  have harg : Complex.arg x.1 = β * t.1 :=
    sectorPolar_arg hr.1 ⟨(neg_neg_of_pos Real.pi_pos).trans hangle.1,
      hangle.2.le.trans hβπ⟩
  have hfx : f x = z := by
    apply C.chart.injOn (C.source hxbound) (C.source (hz.trans hρC))
    have hx := hp r ⟨hr.1.le, hr.2.le⟩ t
    have hθeq : lo + flatLinkOrientedAngle forward (β / k) t = θ := by linarith [ht]
    rw [hθeq] at hx
    exact hx.trans he.symm
  refine ⟨x, hfx, mem_interior_closedEuclideanSector_of_strict_arg hβ hβπ
    (harg.symm ▸ hangle), ?_, ?_⟩
  · change 0 < (sectorPolar r (β * t.1)).im
    rw [sectorPolar_im]
    exact mul_pos hr.1 (Real.sin_pos_of_pos_of_lt_pi hangle.1 (hangle.2.trans_le hβπ))
  · change ‖sectorPolar r (β * t.1)‖ < ρ
    rw [sectorPolar_norm hr.1.le]
    exact hr.2

end RepulsiveCoulomb
