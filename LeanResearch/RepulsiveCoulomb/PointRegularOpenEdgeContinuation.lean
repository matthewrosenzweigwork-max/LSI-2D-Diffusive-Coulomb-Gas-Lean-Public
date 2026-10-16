module

public import LeanResearch.RepulsiveCoulomb.PointCleanBoundaryContinuation
public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Actual nonbranching along full flat interior
points, followed by endpoint continuity. The final endpoint may be marked or
singular and is not required to have a full flat chart. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem MetricFlatDiskChart.forward_unique {Y : Type*} [MetricSpace Y] {p x z w : Y}
    (C : MetricFlatDiskChart Y p)
    (hx : x ∈ ball p C.radius) (hz : z ∈ ball p C.radius) (hw : w ∈ ball p C.radius)
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hxd : dist x p = d) (hzr : dist z p = r) (hwr : dist w p = r)
    (hxz : dist x z = d + r) (hxw : dist x w = d + r) : z = w := by
  let X := C.toEuclidean ⟨x, hx⟩
  let Z := C.toEuclidean ⟨z, hz⟩
  let W := C.toEuclidean ⟨w, hw⟩
  have hnorm (q : ball p C.radius) : ‖(C.toEuclidean q).1‖ = dist q.1 p := by
    have h := C.toEuclidean.dist_eq q ⟨p, mem_ball_self C.radius_pos⟩
    change dist (C.toEuclidean q).1 (C.toEuclidean ⟨p, mem_ball_self C.radius_pos⟩).1 = dist q.1 p at h
    rwa [C.center, dist_zero_right] at h
  have he : Z.1 = W.1 := complex_forward_point_unique hd hr
    ((hnorm ⟨x, hx⟩).trans hxd) ((hnorm ⟨z, hz⟩).trans hzr) ((hnorm ⟨w, hw⟩).trans hwr)
    ((C.toEuclidean.dist_eq ⟨x, hx⟩ ⟨z, hz⟩).trans hxz)
    ((C.toEuclidean.dist_eq ⟨x, hx⟩ ⟨w, hw⟩).trans hxw)
  exact congrArg Subtype.val (C.toEuclidean.injective (Subtype.ext he))

theorem pointActualEdges_eq_near_of_eq_full_flat
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (E F : PointGeodesicTreeEdge a y)
    (hEP : ∀ s, E.curve s ∈ P) (hFP : ∀ s, F.curve s ∈ P)
    (hstart : E.start = F.start)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    {t : unitInterval} (ht : 0 < t.1) (he : E.curve t = F.curve t)
    (C : @MetricFlatDiskChart P (pointRegionMetricSpace ha y P) ⟨F.curve t, hFP t⟩) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : unitInterval, |s.1 - t.1| < ε → E.curve s = F.curve s := by
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos
    (pointSmoothConformalEDist_ne_zero ha y E.distinct) (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let ε := min (t.1 / 2) (C.radius / (2 * L))
  have hε : 0 < ε := lt_min (half_pos ht) (div_pos C.radius_pos (by positivity))
  have hεt : ε ≤ t.1 / 2 := min_le_left _ _
  have hεR : ε * L ≤ C.radius / 2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (t.1 / 2) (C.radius / (2 * L))) hL.le
    change ε * L ≤ C.radius / (2 * L) * L at h
    convert h using 1 <;> field_simp [hL.ne'] <;> ring
  let b : unitInterval := ⟨t.1 - ε / 2, by constructor <;> linarith [t.2.2]⟩
  have hbt : b < t := by change t.1 - ε / 2 < t.1; linarith
  have heb := pointActualEdges_eq_prefix_of_eq ha y E F hstart ht he b hbt.le
  let d := (t.1 - b.1) * L
  have hd : 0 < d := mul_pos (sub_pos.mpr hbt) hL
  have hdR : d < C.radius := by dsimp [d, b]; nlinarith [C.radius_pos]
  have hxd : (pointSmoothConformalEDist a y (E.curve b) (F.curve t)).toReal = d := by
    rw [← he, E.geodesic, abs_of_nonneg (sub_nonneg.mpr (show b.1 ≤ t.1 from hbt.le))]
  refine ⟨ε, hε, ?_⟩
  intro s hs
  by_cases hst : s ≤ t
  · exact pointActualEdges_eq_prefix_of_eq ha y E F hstart ht he s hst
  have hts : t < s := lt_of_not_ge hst
  let r := (s.1 - t.1) * L
  have hr : 0 ≤ r := mul_nonneg (sub_nonneg.mpr hts.le) hL.le
  have hrR : r < C.radius := by
    have hs' : s.1 - t.1 < ε := (abs_lt.mp hs).2
    have hm := mul_lt_mul_of_pos_right hs' hL
    dsimp [r]
    linarith [C.radius_pos]
  have hzr : (pointSmoothConformalEDist a y (E.curve s) (F.curve t)).toReal = r := by
    rw [← he, E.geodesic, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from hts.le))]
  have hwr : (pointSmoothConformalEDist a y (F.curve s) (F.curve t)).toReal = r := by
    rw [F.geodesic, ← hspeed, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from hts.le))]
  have hxz : (pointSmoothConformalEDist a y (E.curve b) (E.curve s)).toReal = d + r := by
    rw [E.geodesic, abs_of_nonneg (sub_nonneg.mpr (show b.1 ≤ s.1 from hbt.le.trans hts.le))]
    dsimp [d, r, L]
    ring
  have hxw : (pointSmoothConformalEDist a y (E.curve b) (F.curve s)).toReal = d + r := by
    rw [heb, F.geodesic, ← hspeed, abs_of_nonneg (sub_nonneg.mpr (show b.1 ≤ s.1 from hbt.le.trans hts.le))]
    dsimp [d, r, L]
    ring
  have hpEq : (⟨E.curve s, hEP s⟩ : P) = ⟨F.curve s, hFP s⟩ :=
    C.forward_unique (x := ⟨E.curve b, hEP b⟩) (z := ⟨E.curve s, hEP s⟩)
      (w := ⟨F.curve s, hFP s⟩) (hxd.trans_lt hdR) (hzr.trans_lt hrR) (hwr.trans_lt hrR)
      hd hr hxd hzr hwr hxz hxw
  exact congrArg Subtype.val hpEq

/-- Agreement propagates to the closed final endpoint even if that endpoint
is the first marked cone. Only the open positive reference segment is flat. -/
theorem pointActualEdges_eq_of_initial_overlap_full_flat_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (E F : PointGeodesicTreeEdge a y)
    (hEP : ∀ s, E.curve s ∈ P) (hFP : ∀ s, F.curve s ∈ P)
    (hstart : E.start = F.start)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    (hflat : ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) ⟨F.curve t, hFP t⟩))
    (hoverlap : ∃ t : unitInterval, 0 < t.1 ∧ E.curve t = F.curve t) : E.curve = F.curve := by
  obtain ⟨v, hv, he⟩ := hoverlap
  by_cases hv1 : v = 1
  · have hcurve : E.curve (1 : unitInterval) = F.curve 1 := by
      simpa only [hv1] using he
    have hfinish : E.finish = F.finish :=
      E.curve_finish.symm.trans (hcurve.trans F.curve_finish)
    have hdF := F.geodesic
    rw [← hstart, ← hfinish] at hdF
    exact pointConformal_geodesic_unique ha y E.start E.finish E.curve F.curve
      E.curve_start E.curve_finish (F.curve_start.trans hstart.symm)
      (F.curve_finish.trans hfinish.symm) E.geodesic hdF
  have hvlt : v.1 < 1 := lt_of_le_of_ne v.2.2 (fun h ↦ hv1 (Subtype.ext h))
  let T := Ioo (0 : ℝ) 1
  let embed : T → unitInterval := fun t ↦ ⟨t.1, t.2.1.le, t.2.2.le⟩
  have hc : Continuous embed := continuous_subtype_val.subtype_mk _
  let S : Set T := {t | E.curve (embed t) = F.curve (embed t)}
  have hclosed : IsClosed S := isClosed_eq (E.continuous.comp hc) (F.continuous.comp hc)
  have hopen : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    intro t ht
    obtain ⟨C⟩ := hflat (embed t) t.2.1 t.2.2
    obtain ⟨ε, hε, hnear⟩ := pointActualEdges_eq_near_of_eq_full_flat ha y E F hEP hFP
      hstart hspeed t.2.1 ht C
    exact ⟨ε, hε, fun s hs ↦ hnear (embed s) hs⟩
  have hnonempty : S.Nonempty := ⟨⟨v.1, hv, hvlt⟩, he⟩
  letI : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Ioo
  have hfull : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have heq : EqOn E.curve F.curve (Iio (1 : unitInterval)) := by
    intro t ht
    by_cases ht0 : t.1 = 0
    · have htzero : t = 0 := Subtype.ext ht0
      rw [htzero]
      exact E.curve_start.trans (hstart.trans F.curve_start.symm)
    · have htp : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      have hm : (⟨t.1, htp, ht⟩ : T) ∈ S := by rw [hfull]; trivial
      exact hm
  have hclosure : closure (Iio (1 : unitInterval)) = Iic 1 :=
    closure_Iio' ⟨0, by norm_num⟩
  funext t
  exact heq.closure E.continuous F.continuous (by rw [hclosure]; exact t.2.2)

end RepulsiveCoulomb
