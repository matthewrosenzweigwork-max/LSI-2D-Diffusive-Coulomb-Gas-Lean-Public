module

public import LeanResearch.RepulsiveCoulomb.ClassicalConeFlatArcRigidity
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkRadialTrace

@[expose] public section

/-! Isolated, uncompiled author draft. The input is an actual isometric map
of a literal bounded Euclidean sector. The output chart and its normalized
polar formula are constructed; no occupied-link assertion is a hypothesis. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def flatLinkOrientedAngle (forward : Bool) (width : ℝ) (t : unitInterval) : ℝ :=
  if forward then width * t.1 else width * (1 - t.1)

theorem flatLinkOrientedAngle_mem (forward : Bool) {width : ℝ} (hw : 0 ≤ width)
    (t : unitInterval) : flatLinkOrientedAngle forward width t ∈ Icc 0 width := by
  cases forward
  · exact ⟨mul_nonneg hw (sub_nonneg.mpr t.2.2),
      mul_le_of_le_one_right hw (by linarith [t.2.1])⟩
  · exact ⟨mul_nonneg hw t.2.1, mul_le_of_le_one_right hw t.2.2⟩

theorem flatLinkOrientedAngle_surjective (forward : Bool) {width θ : ℝ}
    (hw : 0 < width) (hθ : θ ∈ Icc 0 width) :
    ∃ t : unitInterval, flatLinkOrientedAngle forward width t = θ := by
  let u : unitInterval := ⟨θ / width, div_nonneg hθ.1 hw.le, (div_le_one hw).mpr hθ.2⟩
  cases forward
  · refine ⟨unitInterval.symm u, ?_⟩
    simp only [flatLinkOrientedAngle, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
    change width * (1 - (1 - θ / width)) = θ
    field_simp [hw.ne'] <;> ring
  · refine ⟨u, ?_⟩
    change width * (θ / width) = θ
    exact mul_div_cancel₀ _ hw.ne'

/-- The exact radial formula, normalized to the literal coordinate interval
[0, beta / (1 + coalescedExponent/2)]. The Boolean records which source edge
is the lower chart-angle edge; it is derived, not chosen as an input. -/
theorem exists_pointFlatLinkDisk_normalized_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    ∃ C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)),
      ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρL : ρ ≤ L,
        ρ ≤ C.radius ∧ ∃ forward : Bool, ∀ s t : unitInterval,
          C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
            ⟨mul_nonneg hρ.le s.2.1,
              (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
          sectorPolar (ρ * s.1) (flatLinkOrientedAngle forward
            (β / (coalescedPointExponent a y
              (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2 + 1)) t) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y p
  let ρ := min L C.radius
  have hρ : 0 < ρ := lt_min hL C.radius_pos
  have hρL : ρ ≤ L := min_le_left _ _
  have hρC : ρ ≤ C.radius := min_le_right _ _
  let q := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩
  let v (t : unitInterval) := C.chart (f (q t))
  have hb (t : unitInterval) : (pointSmoothConformalEDist a y (f (q t)) p).toReal ≤ C.radius := by
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
  obtain ⟨φ, hφc, hφi, hφpolar, horientation⟩ :=
    classicalCone_flat_arc_directed_lift hα hρ hβ hβπ hvc hvnorm hvdist
  let width := β / (coalescedPointExponent a y p / 2 + 1)
  obtain ⟨b, forward, horient⟩ : ∃ b : ℝ, ∃ forward : Bool,
      ∀ t, b + φ t = flatLinkOrientedAngle forward width t := by
    rcases horientation with hpos | hneg
    · refine ⟨-φ 0, true, fun t ↦ ?_⟩
      rw [hpos t]
      simp [flatLinkOrientedAngle, width]
    · refine ⟨-φ 0 + width, false, fun t ↦ ?_⟩
      rw [hneg t]
      simp only [flatLinkOrientedAngle, Bool.false_eq_true, ↓reduceIte]
      dsimp [width]
      ring
  refine ⟨C.rotate b, ρ, hρ, hρL, hρC, forward, ?_⟩
  intro s t
  rw [PointFlatLinkConeDisk.rotate_apply,
    pointFlatLinkDiskMap_radial y hβ hβπ hL f hd C hρ hρL hρC s t]
  change conePhase b * (s.1 • v t) = sectorPolar (ρ * s.1)
    (flatLinkOrientedAngle forward width t)
  rw [hφpolar t]
  calc
    conePhase b * (s.1 • sectorPolar ρ (φ t)) =
        s.1 • (conePhase b * sectorPolar ρ (φ t)) := by
      simp only [Complex.real_smul]
      ring
    _ = s.1 • sectorPolar ρ (b + φ t) := by rw [conePhase_mul_sectorPolar]
    _ = sectorPolar (ρ * s.1) (b + φ t) := by
      simp only [sectorPolar, Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = _ := by rw [horient t]

end RepulsiveCoulomb
