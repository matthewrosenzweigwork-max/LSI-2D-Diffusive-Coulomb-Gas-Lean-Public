module

public import LeanResearch.RepulsiveCoulomb.PointRetainedActualInitialAngle
public import LeanResearch.RepulsiveCoulomb.ComplexLocalGeodesicStraightness
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! ISOLATED SOURCE-ONLY COMPANION, begun 2026-10-03 12:56 UTC.
No compiler invocation, canonical staging, or acceptance claim.
The dependency PointRetainedActualInitialAngle is the immutable outside draft.

Actual minimizing edges cannot separate after a positive overlap when the
reference edge has genuine retained flat charts at its positive points. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Equality in the Euclidean triangle inequality determines the oriented
forward continuation. No sign or tangent-direction certificate is supplied. -/
theorem complex_forward_point_unique
    {x z w : ℂ} {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hx : ‖x‖ = d) (hz : ‖z‖ = r) (hw : ‖w‖ = r)
    (hxz : dist x z = d + r) (hxw : dist x w = d + r) : z = w := by
  have hdr : d + r ≠ 0 := (add_pos_of_pos_of_nonneg hd hr).ne'
  have ht : d / (d + r) ≠ 0 := div_ne_zero hd.ne' hdr
  have hzero (v : ℂ) (hv : ‖v‖ = r) (hxv : dist x v = d + r) :
      (0 : ℂ) = AffineMap.lineMap x v (d / (d + r)) := by
    apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
    · rw [dist_zero_right, hx, hxv]
      field_simp
    · rw [dist_zero_left, hv, hxv]
      field_simp
      ring
  have he := (hzero z hz hxz).symm.trans (hzero w hw hxw)
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at he
  exact smul_right_injective ℂ ht (add_left_cancel he)

/-- Literal inverse halfdisk/sector charts give local nonbranching in the
actual metric, including intrinsically flat boundaries with singular ambient
cone exponent. Only the proved chart isometry and its full image are used. -/
theorem PointRetainedConeNeighborhood.flat_forward_unique
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {q x z w : ℂ}
    (C : PointRetainedConeNeighborhood a y P q)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi)
    (hx : x ∈ P) (hz : z ∈ P) (hw : w ∈ P)
    (hxR : (pointSmoothConformalEDist a y x q).toReal ≤ C.radius)
    (hzR : (pointSmoothConformalEDist a y z q).toReal ≤ C.radius)
    (hwR : (pointSmoothConformalEDist a y w q).toReal ≤ C.radius)
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hxd : (pointSmoothConformalEDist a y x q).toReal = d)
    (hzr : (pointSmoothConformalEDist a y z q).toReal = r)
    (hwr : (pointSmoothConformalEDist a y w q).toReal = r)
    (hxz : (pointSmoothConformalEDist a y x z).toReal = d + r)
    (hxw : (pointSmoothConformalEDist a y x w).toReal = d + r) : z = w := by
  obtain ⟨X, hX, hXi⟩ := C.flatInverse_surjOn hwidth ⟨hx, hxR⟩
  obtain ⟨Z, hZ, hZi⟩ := C.flatInverse_surjOn hwidth ⟨hz, hzR⟩
  obtain ⟨W, hW, hWi⟩ := C.flatInverse_surjOn hwidth ⟨hw, hwR⟩
  have hzero : (0 : ℂ) ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    simp only [retainedFlatSectorDisk, mem_inter_iff, closedEuclideanSector, mem_setOf_eq,
      Complex.arg_zero, norm_zero]
    exact ⟨⟨le_rfl, C.flatPhysicalWidth_pos.le⟩, C.radius_pos.le⟩
  have hXnorm : ‖X‖ = d := by
    have h := C.flatInverse_dist hwidth hX hzero
    rw [hXi, C.flatInverse_zero, dist_zero_right] at h
    exact h.symm.trans hxd
  have hZnorm : ‖Z‖ = r := by
    have h := C.flatInverse_dist hwidth hZ hzero
    rw [hZi, C.flatInverse_zero, dist_zero_right] at h
    exact h.symm.trans hzr
  have hWnorm : ‖W‖ = r := by
    have h := C.flatInverse_dist hwidth hW hzero
    rw [hWi, C.flatInverse_zero, dist_zero_right] at h
    exact h.symm.trans hwr
  have hXZ : dist X Z = d + r := by
    have h := C.flatInverse_dist hwidth hX hZ
    rw [hXi, hZi] at h
    exact h.symm.trans hxz
  have hXW : dist X W = d + r := by
    have h := C.flatInverse_dist hwidth hX hW
    rw [hXi, hWi] at h
    exact h.symm.trans hxw
  have he := complex_forward_point_unique hd hr hXnorm hZnorm hWnorm hXZ hXW
  exact hZi.symm.trans ((congrArg C.flatInverse he).trans hWi)

/-- A shared positive parameter forces equality of the literal prefixes by
actual fixed-endpoint uniqueness. No continuation uniqueness is assumed. -/
theorem pointActualEdges_eq_prefix_of_eq
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E F : PointGeodesicTreeEdge a y) (hstart : E.start = F.start)
    {t : unitInterval} (ht : 0 < t.1) (he : E.curve t = F.curve t) :
    ∀ s : unitInterval, s ≤ t → E.curve s = F.curve s := by
  let E' := pointGeodesicSubedge ha y E 0 t ht
  let F' := pointGeodesicSubedge ha y F 0 t ht
  have hleft : E'.start = F'.start := by
    change E.curve 0 = F.curve 0
    exact E.curve_start.trans (hstart.trans F.curve_start.symm)
  have hright : E'.finish = F'.finish := he
  have hdF := F'.geodesic
  rw [← hleft, ← hright] at hdF
  have hcurves : E'.curve = F'.curve :=
    pointConformal_geodesic_unique ha y E'.start E'.finish E'.curve F'.curve
      E'.curve_start E'.curve_finish (F'.curve_start.trans hleft.symm)
      (F'.curve_finish.trans hright.symm) E'.geodesic hdF
  intro s hst
  have hsrange : s ∈ range (pointEdgeSubparam 0 t) := by
    rw [pointEdgeSubparam_range (show (0 : unitInterval) < t from ht)]
    exact ⟨s.2.1, hst⟩
  obtain ⟨u, hu⟩ := hsrange
  have h := congrFun hcurves u
  change E.curve (pointEdgeSubparam 0 t u) = F.curve (pointEdgeSubparam 0 t u) at h
  rwa [hu] at h

/-- A genuine local flat chart makes any common positive point an open
interval of common points. The incoming anchor comes from actual prefix
uniqueness; the outgoing point is determined by actual metric distances. -/
theorem pointActualEdges_eq_near_of_eq_flat
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (E F : PointGeodesicTreeEdge a y)
    (hEP : ∀ s, E.curve s ∈ P) (hFP : ∀ s, F.curve s ∈ P)
    (hstart : E.start = F.start)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    {t : unitInterval} (ht : 0 < t.1) (he : E.curve t = F.curve t)
    (C : PointRetainedConeNeighborhood a y P (F.curve t))
    (hwidth : C.flatPhysicalWidth ≤ Real.pi) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : unitInterval, |s.1 - t.1| < ε →
      E.curve s = F.curve s := by
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos
    (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let ε := min (t.1 / 2) (C.radius / (2 * L))
  have hε : 0 < ε := lt_min (half_pos ht) (div_pos C.radius_pos (by positivity))
  have hεt : ε ≤ t.1 / 2 := min_le_left _ _
  have hεR : ε * L ≤ C.radius / 2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (t.1 / 2)
      (C.radius / (2 * L))) hL.le
    change ε * L ≤ C.radius / (2 * L) * L at h
    convert h using 1 <;> field_simp [hL.ne'] <;> ring
  let b : unitInterval := ⟨t.1 - ε / 2,
    by constructor <;> linarith [t.2.2]⟩
  have hbt : b < t := by change t.1 - ε / 2 < t.1; linarith
  have heb : E.curve b = F.curve b :=
    pointActualEdges_eq_prefix_of_eq ha y E F hstart ht he b hbt.le
  let d := (t.1 - b.1) * L
  have hd : 0 < d := mul_pos (sub_pos.mpr hbt) hL
  have hdR : d ≤ C.radius := by
    dsimp [d, b]
    nlinarith [C.radius_pos]
  have hxd : (pointSmoothConformalEDist a y (E.curve b) (F.curve t)).toReal = d := by
    rw [← he, E.geodesic, abs_of_nonneg (sub_nonneg.mpr (show b.1 ≤ t.1 from hbt.le))]
  refine ⟨ε, hε, ?_⟩
  intro s hs
  by_cases hst : s ≤ t
  · exact pointActualEdges_eq_prefix_of_eq ha y E F hstart ht he s hst
  have hts : t < s := lt_of_not_ge hst
  let r := (s.1 - t.1) * L
  have hr : 0 ≤ r := mul_nonneg (sub_nonneg.mpr hts.le) hL.le
  have hrR : r ≤ C.radius := by
    have hs' : s.1 - t.1 < ε := (abs_lt.mp hs).2
    have hm := mul_lt_mul_of_pos_right hs' hL
    dsimp [r]
    linarith [C.radius_pos]
  have hzr : (pointSmoothConformalEDist a y (E.curve s) (F.curve t)).toReal = r := by
    rw [← he, E.geodesic, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from hts.le))]
  have hwr : (pointSmoothConformalEDist a y (F.curve s) (F.curve t)).toReal = r := by
    rw [F.geodesic, ← hspeed, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from hts.le))]
  have hxz : (pointSmoothConformalEDist a y (E.curve b) (E.curve s)).toReal = d + r := by
    rw [E.geodesic, abs_of_nonneg (sub_nonneg.mpr
      (show b.1 ≤ s.1 from hbt.le.trans hts.le))]
    dsimp [d, r, L]
    ring
  have hxw : (pointSmoothConformalEDist a y (E.curve b) (F.curve s)).toReal = d + r := by
    rw [heb, F.geodesic, ← hspeed, abs_of_nonneg (sub_nonneg.mpr
      (show b.1 ≤ s.1 from hbt.le.trans hts.le))]
    dsimp [d, r, L]
    ring
  exact C.flat_forward_unique hwidth (hEP b) (hEP s) (hFP s)
    (hxd.le.trans hdR) (hzr.le.trans hrR) (hwr.le.trans hrR)
    hd hr hxd hzr hwr hxz hxw

/-- Positive initial overlap propagates along a genuinely intrinsically flat
reference boundary edge. This is a theorem about the actual paths and actual
retained charts, not a nonbranching/continuation certificate. -/
theorem pointActualEdges_eq_of_initial_overlap_flat
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (E F : PointGeodesicTreeEdge a y)
    (hEP : ∀ s, E.curve s ∈ P) (hFP : ∀ s, F.curve s ∈ P)
    (hstart : E.start = F.start)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    (hflat : ∀ t : unitInterval, 0 < t.1 →
      ∃ C : PointRetainedConeNeighborhood a y P (F.curve t),
        C.flatPhysicalWidth ≤ Real.pi)
    (hoverlap : ∃ t : unitInterval, 0 < t.1 ∧ E.curve t = F.curve t) :
    E.curve = F.curve := by
  let T := Ioc (0 : ℝ) 1
  let embed : T → unitInterval := fun t ↦ ⟨t.1, t.2.1.le, t.2.2⟩
  have hc : Continuous embed := continuous_subtype_val.subtype_mk _
  let D : Set T := {t | E.curve (embed t) = F.curve (embed t)}
  have hclosed : IsClosed D := isClosed_eq (E.continuous.comp hc) (F.continuous.comp hc)
  have hopen : IsOpen D := by
    apply Metric.isOpen_iff.mpr
    intro t ht
    obtain ⟨C, hC⟩ := hflat (embed t) t.2.1
    obtain ⟨ε, hε, hnear⟩ := pointActualEdges_eq_near_of_eq_flat
      ha y E F hEP hFP hstart hspeed t.2.1 ht C hC
    refine ⟨ε, hε, ?_⟩
    intro s hs
    apply hnear (embed s)
    exact hs
  have hnonempty : D.Nonempty := by
    obtain ⟨t, ht, he⟩ := hoverlap
    exact ⟨⟨t.1, ht, t.2.2⟩, he⟩
  letI : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Ioc
  have hfull : D = univ := (show IsClopen D from ⟨hclosed, hopen⟩).eq_univ hnonempty
  funext t
  by_cases ht : t.1 = 0
  · have ht0 : t = (0 : unitInterval) := Subtype.ext ht
    rw [ht0]
    exact E.curve_start.trans (hstart.trans F.curve_start.symm)
  · have htpos : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have hmem : (⟨t.1, htpos, t.2.2⟩ : T) ∈ D := by rw [hfull]; trivial
    exact hmem

end RepulsiveCoulomb
