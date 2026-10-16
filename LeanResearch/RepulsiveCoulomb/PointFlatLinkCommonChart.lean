import LeanResearch.RepulsiveCoulomb.PointFlatLinkNormalizedPolar

/-! SOURCE-ONLY, UNCOMPILED. Fixed-chart version of the actual flat-sector
occupation formula. Several incident sector/halfdisk embeddings can now be
read in one prescribed full cone chart, so their angular order is genuinely
comparable. No interval order, target occupation width, or chart transition
is supplied as an input. Passing halfdisks use beta = pi. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointFlatLinkDisk_fixed_chart_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∃ forward : Bool, ∀ s t : unitInterval,
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
        ⟨mul_nonneg hρ.le s.2.1,
          (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
        sectorPolar (ρ * s.1) (lo + flatLinkOrientedAngle forward
          (β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let q := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩
  let v (t : unitInterval) := C.chart (f (q t))
  have hb (t : unitInterval) :
      (pointSmoothConformalEDist a y (f (q t)) p).toReal ≤ C.radius := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar ρ (β * t.1)‖ ≤ C.radius
    rw [sectorPolar_norm hρ.le]
    exact hρC
  have hfc := continuous_pointFlatLinkDiskMap ha y f hd
  have hqc : Continuous q := continuous_flatLinkSectorDiskPoint hβ.le hβπ ⟨hρ.le, hρL⟩
  have hvc : Continuous v := C.chart.continuousOn.comp_continuous (hfc.comp hqc)
    (fun t ↦ C.source (hb t))
  have hvnorm (t : unitInterval) : ‖v t‖ = ρ := by
    rw [C.norm_chart (hb t), pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hρ.le _
  have hα : 0 ≤ coalescedPointExponent a y p / 2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hvdist (s t : unitInterval) :
      @dist ℂ (classicalConeMetricSpace (coalescedPointExponent a y p / 2) hα).toDist
        (v s) (v t) = ‖sectorPolar ρ (β * s.1) - sectorPolar ρ (β * t.1)‖ := by
    change pointClassicalConeDist a y p (C.chart (f (q s))) (C.chart (f (q t))) = _
    rw [← C.metric (f (q s)) (hb s) (f (q t)) (hb t), hd]
    change dist (sectorPolar ρ (β * s.1)) (sectorPolar ρ (β * t.1)) = _
    exact dist_eq_norm _ _
  obtain ⟨φ, _, _, hφpolar, horientation⟩ :=
    classicalCone_flat_arc_directed_lift hα hρ hβ hβπ hvc hvnorm hvdist
  let width := β / (coalescedPointExponent a y p / 2 + 1)
  obtain ⟨lo, forward, horient⟩ : ∃ lo : ℝ, ∃ forward : Bool,
      ∀ t, φ t = lo + flatLinkOrientedAngle forward width t := by
    rcases horientation with hpos | hneg
    · exact ⟨φ 0, true, by simpa only [flatLinkOrientedAngle, ↓reduceIte] using hpos⟩
    · refine ⟨φ 0 - width, false, fun t ↦ ?_⟩
      rw [hneg t]
      simp only [flatLinkOrientedAngle, Bool.false_eq_true, ↓reduceIte]
      dsimp [width]
      ring
  refine ⟨lo, forward, fun s t ↦ ?_⟩
  rw [pointFlatLinkDiskMap_radial y hβ hβπ hL f hd C hρ hρL hρC s t]
  change s.1 • v t = sectorPolar (ρ * s.1)
    (lo + flatLinkOrientedAngle forward width t)
  rw [hφpolar t, horient t]
  simp only [sectorPolar, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Literal occupied interval in the prescribed common chart, including both
edges and the center. Distinct incident pieces can therefore be compared
without silently replacing the ambient link by a shorter circular angle. -/
theorem exists_pointFlatLinkDisk_fixed_chart_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∀ z,
      (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
        (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo
          (lo + β / (coalescedPointExponent a y
            (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1))) := by
  obtain ⟨lo, forward, hpolar⟩ := exists_pointFlatLinkDisk_fixed_chart_polar
    ha y hβ hβπ hL f hd C hρ hρL hρC
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by
    dsimp [k]
    linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β / k := div_pos hβ hk
  refine ⟨lo, fun z hz ↦ ?_⟩
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

end RepulsiveCoulomb
