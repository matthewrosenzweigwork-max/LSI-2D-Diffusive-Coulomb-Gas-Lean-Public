import LeanResearch.RepulsiveCoulomb.PointBoundedCornerRetainedChart
import LeanResearch.RepulsiveCoulomb.PointSectorReturnPhysicalDirectionLink

/-! SOURCE-ONLY, UNCOMPILED. The translated line's actual full direction is
constructed from a literal isometric halfdisk, its backward old-edge germ, and
its interior source ray. No ambient exponent zero, target angle identity,
selected cap, or budget-direction hypothesis is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The source ray making angle beta with the backward old edge. -/
def parallelHalfDiskDirection {β : ℝ} (hβ : 0 < β) (hβπ : β < Real.pi) : unitInterval :=
  ⟨β / Real.pi, (div_pos hβ Real.pi_pos).le,
    ((div_lt_one Real.pi_pos).mpr hβπ).le⟩

/-- Identify the actual metric-edge direction from the same source halfdisk.
The source's angular parameter is beta/pi. Both possible chart orientations
are derived from the actual old-edge frontier germ. -/
theorem pointRetainedParallelHalfDisk_construct_direction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {L β : ℝ} (hL : 0 < L) (hβ : 0 < β) (hβπ : β < Real.pi)
    (f : flatLinkSectorDisk Real.pi L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)))
    (hC : C.Admissible) (outgoing backward : ℝ → ℂ)
    (hback : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs, hsL⟩ 0) = backward s)
    (hout : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs, hsL⟩
        (parallelHalfDiskDirection hβ hβπ)) = outgoing s)
    (E : PointGeodesicTreeEdge a y)
    (hE0 : E.start = f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))
    (hEP : ∀ t, E.curve t ∈ P)
    (hEcurve : ∀ t : unitInterval, E.curve t = outgoing (pointActualEdgeLength E * t.1))
    {R : ℝ} (hR : 0 < R) (hRL : R ≤ L) (hRC : R < C.radius)
    (hfront : backward R ∈ frontier P) :
    ∃ ξ : ℝ, ξ ∈ Icc C.lo C.hi ∧ (ξ = C.lo ∨ ξ = C.hi) ∧
      C.actualInitialRawAngle ha y hC E hE0 hEP ∈ Ioo C.lo C.hi ∧
      (1 + coalescedPointExponent a y (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) / 2) *
        |C.actualInitialRawAngle ha y hC E hE0 hEP - ξ| = β ∧
      ∀ t ∈ Ioo (0 : ℝ) R, backward t ∈ C.chart.source ∧
        C.chart (backward t) = pointRadialSectorPoint t ξ := by
  let p := f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hkcomm : 1 + coalescedPointExponent a y
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) / 2 = k := by
    dsimp [k, p]
    ring
  have hβk : 0 < β / k := div_pos hβ hk
  have hπk : β / k < Real.pi / k := (div_lt_div_iff_of_pos_right hk).mpr hβπ
  have hβscale : (Real.pi / k) * (parallelHalfDiskDirection hβ hβπ).1 = β / k := by
    change (Real.pi / k) * (β / Real.pi) = β / k
    field_simp [Real.pi_ne_zero, hk.ne'] <;> ring
  have hfirst : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl R ⟨hR.le, hRL⟩ 0) ∈ frontier P := by
    rw [hback R hR.le hRL]
    exact hfront
  have hgerm (A : unitInterval → ℝ)
      (hpolar : ∀ s t : unitInterval, C.chart (f
        (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (R * s.1)
          ⟨mul_nonneg hR.le s.2.1, (mul_le_of_le_one_right hR.le s.2.2).trans hRL⟩ t)) =
        sectorPolar (R * s.1) (A t))
      (t : unitInterval) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) R) :
      C.chart (f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl u
        ⟨hu.1.le, hu.2.le.trans hRL⟩ t)) = pointRadialSectorPoint u (A t) := by
    let s : unitInterval := ⟨u / R, div_nonneg hu.1.le hR.le, (div_le_one hR).mpr hu.2.le⟩
    have hus : R * s.1 = u := mul_div_cancel₀ _ hR.ne'
    have he := hpolar s t
    have hp : flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (R * s.1)
        ⟨mul_nonneg hR.le s.2.1, (mul_le_of_le_one_right hR.le s.2.2).trans hRL⟩ t =
        flatLinkSectorDiskPoint Real.pi_pos.le le_rfl u ⟨hu.1.le, hu.2.le.trans hRL⟩ t := by
      apply Subtype.ext
      change sectorPolar (R * s.1) (Real.pi * t.1) = sectorPolar u (Real.pi * t.1)
      rw [hus]
    rw [hp, hus, sectorPolar_eq_pointRadialSectorPoint] at he
    exact he
  have hbackSource (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) R) : backward u ∈ C.chart.source := by
    apply C.source
    change (pointSmoothConformalEDist a y (backward u)
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal ≤ C.radius
    rw [← hback u hu.1.le (hu.2.le.trans hRL), pointFlatLinkDiskMap_dist_apex y Real.pi_pos hL f hd]
    change ‖sectorPolar u (Real.pi * (0 : unitInterval).1)‖ ≤ C.radius
    rw [sectorPolar_norm hu.1.le]
    exact hu.2.le.trans hRC.le
  rcases pointFlatLinkDisk_first_edge_endpoint Real.pi_pos le_rfl hL f hd hfP C
      hR hRL hRC hfirst with hlo | hhi
  · obtain ⟨hcutHi, hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y Real.pi_pos le_rfl hL
      f hd hfP C hC hR hRL hRC.le hlo
    have hbackGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (backward u) = pointRadialSectorPoint u C.lo := by
      intro u hu
      have he := hgerm (fun t ↦ C.lo + (Real.pi / k) * t.1) hpolar 0 u hu
      have hb := congrArg C.chart (hback u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_zero, mul_zero, add_zero] using hb.symm.trans he
    have houtGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (outgoing u) = pointRadialSectorPoint u (C.lo + β / k) := by
      intro u hu
      have he := hgerm (fun t ↦ C.lo + (Real.pi / k) * t.1) hpolar
        (parallelHalfDiskDirection hβ hβπ) u hu
      have ho := congrArg C.chart (hout u hu.1.le (hu.2.le.trans hRL))
      simpa only [hβscale] using ho.symm.trans he
    have hcutLo : C.lo < C.lo + β / k := lt_add_of_pos_right _ hβk
    have hcut : C.lo + β / k < C.hi := by change C.lo + Real.pi / k ≤ C.hi at hcutHi; linarith
    have hraw := C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP outgoing hEcurve
      hR ⟨hcutLo.le, hcut.le⟩ houtGerm
    refine ⟨C.lo, ⟨le_rfl, C.width_pos.le⟩, Or.inl rfl,
      hraw.symm ▸ And.intro hcutLo hcut, ?_, ?_⟩
    · rw [hraw, add_sub_cancel_left, abs_of_pos hβk]
      rw [hkcomm]
      exact mul_div_cancel₀ _ hk.ne'
    · exact fun u hu ↦ ⟨hbackSource u hu, hbackGerm u hu⟩
  · obtain ⟨hcutLo, hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y Real.pi_pos le_rfl hL
      f hd hfP C hC hR hRL hRC.le hhi
    have hbackGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (backward u) = pointRadialSectorPoint u C.hi := by
      intro u hu
      have he := hgerm (fun t ↦ C.hi - (Real.pi / k) * t.1) hpolar 0 u hu
      have hb := congrArg C.chart (hback u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_zero, mul_zero, sub_zero] using hb.symm.trans he
    have houtGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (outgoing u) = pointRadialSectorPoint u (C.hi - β / k) := by
      intro u hu
      have he := hgerm (fun t ↦ C.hi - (Real.pi / k) * t.1) hpolar
        (parallelHalfDiskDirection hβ hβπ) u hu
      have ho := congrArg C.chart (hout u hu.1.le (hu.2.le.trans hRL))
      simpa only [hβscale] using ho.symm.trans he
    have hcutHi : C.hi - β / k < C.hi := sub_lt_self _ hβk
    have hcut : C.lo < C.hi - β / k := by change C.lo ≤ C.hi - Real.pi / k at hcutLo; linarith
    have hraw := C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP outgoing hEcurve
      hR ⟨hcut.le, hcutHi.le⟩ houtGerm
    refine ⟨C.hi, ⟨C.width_pos.le, le_rfl⟩, Or.inr rfl,
      hraw.symm ▸ And.intro hcut hcutHi, ?_, ?_⟩
    · rw [hraw, show C.hi - β / k - C.hi = -(β / k) by ring, abs_neg, abs_of_pos hβk]
      rw [hkcomm]
      exact mul_div_cancel₀ _ hk.ne'
    · exact fun u hu ↦ ⟨hbackSource u hu, hbackGerm u hu⟩

end RepulsiveCoulomb
