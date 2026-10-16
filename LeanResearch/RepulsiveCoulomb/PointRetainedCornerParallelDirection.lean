import LeanResearch.RepulsiveCoulomb.PointRetainedParallelHalfDiskDirection

/-! SOURCE-ONLY, UNCOMPILED. The actual occupied corner of angle beta has
its last source ray strictly inside the full retained interval whenever the
remaining angle is positive. This handles marked attachment origins; no full
pi halfdisk or zero original coefficient is needed. Both chart orientations
and the occupied physical direction are outputs of the actual corner map. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointRetainedCorner_construct_parallel_direction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {L β : ℝ} (hL : 0 < L) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth) (outgoing backward : ℝ → ℂ)
    (hback : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsL⟩ 0) = backward s)
    (hout : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsL⟩
        1) = outgoing s)
    (E : PointGeodesicTreeEdge a y)
    (hE0 : E.start = f (flatLinkSectorDiskApex hβ.le hL.le))
    (hEP : ∀ t, E.curve t ∈ P)
    (hEcurve : ∀ t : unitInterval, E.curve t = outgoing (pointActualEdgeLength E * t.1))
    {R : ℝ} (hR : 0 < R) (hRL : R ≤ L) (hRC : R < C.radius)
    (hfront : backward R ∈ frontier P) :
    ∃ ξ : ℝ, ξ ∈ Icc C.lo C.hi ∧ (ξ = C.lo ∨ ξ = C.hi) ∧
      C.actualInitialRawAngle ha y hC E hE0 hEP ∈ Ioo C.lo C.hi ∧
      (1 + coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le)) / 2) *
        |C.actualInitialRawAngle ha y hC E hE0 hEP - ξ| = β ∧
      ∀ t ∈ Ioo (0 : ℝ) R, backward t ∈ C.chart.source ∧
        C.chart (backward t) = pointRadialSectorPoint t ξ := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hβk : 0 < β / k := div_pos hβ hk
  have hβwidth : β / k < C.hi - C.lo := by
    apply (div_lt_iff₀ hk).mpr
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,k,p,mul_comm] using hremain
  have hfirst : f (flatLinkSectorDiskPoint hβ.le hβπ R ⟨hR.le, hRL⟩ 0) ∈ frontier P := by
    rw [hback R hR.le hRL]
    exact hfront
  have hgerm (A : unitInterval → ℝ)
      (hpolar : ∀ s t : unitInterval, C.chart (f
        (flatLinkSectorDiskPoint hβ.le hβπ (R * s.1)
          ⟨mul_nonneg hR.le s.2.1, (mul_le_of_le_one_right hR.le s.2.2).trans hRL⟩ t)) =
        sectorPolar (R * s.1) (A t))
      (t : unitInterval) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) R) :
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ u
        ⟨hu.1.le, hu.2.le.trans hRL⟩ t)) = pointRadialSectorPoint u (A t) := by
    let s : unitInterval := ⟨u / R, div_nonneg hu.1.le hR.le, (div_le_one hR).mpr hu.2.le⟩
    have hus : R * s.1 = u := mul_div_cancel₀ _ hR.ne'
    have he := hpolar s t
    have hp : flatLinkSectorDiskPoint hβ.le hβπ (R * s.1)
        ⟨mul_nonneg hR.le s.2.1, (mul_le_of_le_one_right hR.le s.2.2).trans hRL⟩ t =
        flatLinkSectorDiskPoint hβ.le hβπ u ⟨hu.1.le, hu.2.le.trans hRL⟩ t := by
      apply Subtype.ext
      change sectorPolar (R * s.1) (β * t.1) = sectorPolar u (β * t.1)
      rw [hus]
    rw [hp, hus, sectorPolar_eq_pointRadialSectorPoint] at he
    exact he
  have hbackSource (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) R) : backward u ∈ C.chart.source := by
    apply C.source
    change (pointSmoothConformalEDist a y (backward u)
      (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ C.radius
    rw [← hback u hu.1.le (hu.2.le.trans hRL), pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar u (β * (0 : unitInterval).1)‖ ≤ C.radius
    rw [sectorPolar_norm hu.1.le]
    exact hu.2.le.trans hRC.le
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hR hRL hRC hfirst with hlo | hhi
  · obtain ⟨hcutHi, hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
      f hd hfP C hC hR hRL hRC.le hlo
    have hbackGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (backward u) = pointRadialSectorPoint u C.lo := by
      intro u hu
      have he := hgerm (fun t ↦ C.lo + (β / k) * t.1) hpolar 0 u hu
      have hb := congrArg C.chart (hback u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_zero, mul_zero, add_zero] using hb.symm.trans he
    have houtGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (outgoing u) = pointRadialSectorPoint u (C.lo + β / k) := by
      intro u hu
      have he := hgerm (fun t ↦ C.lo + (β / k) * t.1) hpolar
        1 u hu
      have ho := congrArg C.chart (hout u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_one, mul_one] using ho.symm.trans he
    have hcutLo : C.lo < C.lo + β / k := lt_add_of_pos_right _ hβk
    have hcut : C.lo + β / k < C.hi := by linarith
    have hraw := C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP outgoing hEcurve
      hR ⟨hcutLo.le, hcut.le⟩ houtGerm
    refine ⟨C.lo, ⟨le_rfl, C.width_pos.le⟩, Or.inl rfl,
      hraw.symm ▸ And.intro hcutLo hcut, ?_, ?_⟩
    · rw [hraw, add_sub_cancel_left, abs_of_pos hβk]
      have he := mul_div_cancel₀ β hk.ne'
      simpa only [k,p,add_comm 1 (coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le))/2)] using he
    · exact fun u hu ↦ ⟨hbackSource u hu, hbackGerm u hu⟩
  · obtain ⟨hcutLo, hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
      f hd hfP C hC hR hRL hRC.le hhi
    have hbackGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (backward u) = pointRadialSectorPoint u C.hi := by
      intro u hu
      have he := hgerm (fun t ↦ C.hi - (β / k) * t.1) hpolar 0 u hu
      have hb := congrArg C.chart (hback u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_zero, mul_zero, sub_zero] using hb.symm.trans he
    have houtGerm : ∀ u ∈ Ioo (0 : ℝ) R,
        C.chart (outgoing u) = pointRadialSectorPoint u (C.hi - β / k) := by
      intro u hu
      have he := hgerm (fun t ↦ C.hi - (β / k) * t.1) hpolar
        1 u hu
      have ho := congrArg C.chart (hout u hu.1.le (hu.2.le.trans hRL))
      simpa only [Set.Icc.coe_one, mul_one] using ho.symm.trans he
    have hcutHi : C.hi - β / k < C.hi := sub_lt_self _ hβk
    have hcut : C.lo < C.hi - β / k := by linarith
    have hraw := C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP outgoing hEcurve
      hR ⟨hcut.le, hcutHi.le⟩ houtGerm
    refine ⟨C.hi, ⟨C.width_pos.le, le_rfl⟩, Or.inr rfl,
      hraw.symm ▸ And.intro hcut hcutHi, ?_, ?_⟩
    · rw [hraw, show C.hi - β / k - C.hi = -(β / k) by ring, abs_neg, abs_of_pos hβk]
      have he := mul_div_cancel₀ β hk.ne'
      simpa only [k,p,add_comm 1 (coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le))/2)] using he
    · exact fun u hu ↦ ⟨hbackSource u hu, hbackGerm u hu⟩


end RepulsiveCoulomb
