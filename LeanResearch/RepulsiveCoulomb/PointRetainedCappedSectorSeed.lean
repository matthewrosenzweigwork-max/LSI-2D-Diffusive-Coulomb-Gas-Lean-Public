import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart
import LeanResearch.RepulsiveCoulomb.PointActualGeodesicContinuation

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03.

Construct a literal positive-radius Euclidean sector in the actual retained
cone chart, even when the retained physical width itself exceeds pi. The
sector width, rather than the whole retained width, is capped by pi.

This constructs the initial two-dimensional map. It does NOT assert its
continuation to an unbounded sector, and it does not assume a sector family.
No compiler invocation or canonical edit was performed by the author.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Shrinking the angular cap is literal set inclusion. -/
theorem retainedFlatSectorDisk_mono_angle {β γ R : ℝ} (h : β ≤ γ) :
    retainedFlatSectorDisk β R ⊆ retainedFlatSectorDisk γ R := by
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans h⟩, hz.2⟩

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

/-- Unlike the full-chart theorem, this only caps the occupied sub-sector.
The retained physical angle may be greater than pi. -/
theorem cappedFlatInverse_dist (C : PointRetainedConeNeighborhood a y P p)
    {β : ℝ} (hβπ : β ≤ Real.pi)
    {x z : ℂ} (hx : x ∈ retainedFlatSectorDisk β C.radius)
    (hz : z ∈ retainedFlatSectorDisk β C.radius) :
    (pointSmoothConformalEDist a y (C.flatInverse x) (C.flatInverse z)).toReal =
      dist x z := by
  obtain ⟨hxR, hrightx⟩ := C.inverse_metricBall
    ((C.flatInverseCoordinate_norm x).trans_le hx.2)
  obtain ⟨hzR, hrightz⟩ := C.inverse_metricBall
    ((C.flatInverseCoordinate_norm z).trans_le hz.2)
  change (pointSmoothConformalEDist a y (C.chart.symm (C.flatInverseCoordinate x))
    (C.chart.symm (C.flatInverseCoordinate z))).toReal = dist x z
  rw [C.metric _ hxR _ hzR, hrightx, hrightz]
  exact (rotated_sectorAngularMap_classicalCone_dist_le_pi
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hβπ
    C.lo hx.1 hz.1).trans (dist_eq_norm x z).symm

/-- An actual bounded sector map, built solely from the retained chart. -/
def cappedFlatSectorChart (C : PointRetainedConeNeighborhood a y P p)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth) :
    retainedFlatSectorDisk β C.radius → P :=
  fun z ↦ ⟨C.flatInverse z.1,
    (C.flatInverse_mem_and_radius (retainedFlatSectorDisk_mono_angle hβwidth z.2)).1⟩

theorem cappedFlatSectorChart_isometry (ha : ∀ j, 0 ≤ a j)
    (C : PointRetainedConeNeighborhood a y P p)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth) (hβπ : β ≤ Real.pi) :
    @Isometry (retainedFlatSectorDisk β C.radius) P
      (inferInstance : PseudoEMetricSpace (retainedFlatSectorDisk β C.radius))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
      (C.cappedFlatSectorChart hβwidth) := by
  apply @Isometry.of_dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  intro x z
  exact C.cappedFlatInverse_dist hβπ x.2 z.2

/-- The exact raw radial endpoint is constructed from the actual inverse
chart, with its genuine metric radius and retained membership. -/
theorem exists_raw_radial_endpoint (C : PointRetainedConeNeighborhood a y P p)
    {r θ : ℝ} (hr : 0 < r) (hrR : r ≤ C.radius)
    (hθ : θ ∈ Icc C.lo C.hi) :
    ∃ z : ℂ, z ∈ P ∧
      (pointSmoothConformalEDist a y z p).toReal = r ∧
      C.chart z = pointRadialSectorPoint r θ := by
  have hw : ‖pointRadialSectorPoint r θ‖ ≤ C.radius := by
    rw [pointRadialSectorPoint_norm hr.le]
    exact hrR
  let z := C.chart.symm (pointRadialSectorPoint r θ)
  obtain ⟨hzR, hzcoord⟩ := C.inverse_metricBall hw
  have hzP : z ∈ P := (C.retained z hzR).mpr (by
    rw [hzcoord]
    exact ⟨r, ⟨hr.le, hrR⟩, θ, hθ, rfl⟩)
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  refine ⟨z, hzP, ?_, hzcoord⟩
  rw [C.metric z hzR p hpR, hzcoord, C.center,
    pointClassicalConeDist_apex, pointRadialSectorPoint_norm hr.le]

/-- Construct a genuine minimizing radial edge for any actual link direction.
No direction selector or pre-existing edge is supplied. The whole edge lies
in the literal retained patch, without invoking global region convexity. -/
theorem exists_raw_radial_seed_edge (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    {r θ : ℝ} (hr : 0 < r) (hrR : r ≤ C.radius)
    (hθ : θ ∈ Icc C.lo C.hi) :
    ∃ E : PointGeodesicTreeEdge a y,
      E.start = p ∧
      (pointSmoothConformalEDist a y E.start E.finish).toReal = r ∧
      (∀ t, E.curve t ∈ P) ∧
      ∀ t, C.chart (E.curve t) = pointRadialSectorPoint (t.1 * r) θ := by
  obtain ⟨z, hzP, hzr, hzcoord⟩ := C.exists_raw_radial_endpoint hr hrR hθ
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hpz : p ≠ z := by
    intro he
    rw [← he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hzr
    exact hr.ne' hzr.symm
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y p z
  have hL : (pointSmoothConformalEDist a y p z).toReal = r := by
    rwa [pointSmoothConformalEDist_comm a y p z]
  have hball (t : unitInterval) :
      (pointSmoothConformalEDist a y (γ t) p).toReal ≤ C.radius := by
    have h := hd t 0
    have hzero : γ (0 : unitInterval) = p := h0
    rw [hzero, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1, hL] at h
    rw [h]
    exact (mul_le_of_le_one_left hr.le t.2.2).trans hrR
  have hrad (t : unitInterval) : C.chart (γ t) = t.1 • C.chart z := by
    apply classicalCone_geodesic_from_apex_nonneg
      (α := coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
      (fun s ↦ C.chart (γ s)) (C.chart z)
      ((congrArg C.chart h0).trans C.center) (congrArg C.chart h1)
    intro s u
    change pointClassicalConeDist a y p (C.chart (γ s)) (C.chart (γ u)) = _
    rw [← C.metric _ (hball s) _ (hball u), hd, hL,
      hzcoord, pointRadialSectorPoint_norm hr.le]
  have hpolar (t : unitInterval) :
      C.chart (γ t) = pointRadialSectorPoint (t.1 * r) θ := by
    rw [hrad t, hzcoord]
    simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hP (t : unitInterval) : γ t ∈ P := by
    apply (C.retained (γ t) (hball t)).mpr
    rw [hpolar t]
    exact ⟨t.1 * r, ⟨mul_nonneg t.2.1 hr.le,
      (mul_le_of_le_one_left hr.le t.2.2).trans hrR⟩, θ, hθ, rfl⟩
  let E : PointGeodesicTreeEdge a y := ⟨p, z, hpz, γ, h0, h1, hc, hd⟩
  exact ⟨E, rfl, hL, hP, hpolar⟩

/-- Every literal link direction has an actual complete ambient minimizing
ray with precisely that initial radial germ. Global retention in P and global
avoidance of marks are deliberately NOT asserted here. -/
theorem exists_raw_direction_complete_ray (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    {r θ : ℝ} (hr : 0 < r) (hrR : r ≤ C.radius)
    (hθ : θ ∈ Icc C.lo C.hi) :
    ∃ γ : NNReal → ℂ, γ 0 = p ∧ Topology.IsClosedEmbedding γ ∧ IsProperMap γ ∧
      (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t) ∧
      ∀ s : NNReal, (s : ℝ) ≤ r →
        γ s ∈ P ∧ C.chart (γ s) = pointRadialSectorPoint s.1 θ := by
  obtain ⟨E, hE0, hEL, hEP, hEpolar⟩ := C.exists_raw_radial_seed_edge ha y hr hrR hθ
  obtain ⟨γ, hγ0, hclosed, hproper, hd, hseed⟩ :=
    exists_pointConformal_prescribed_complete_ray ha y E
  refine ⟨γ, hγ0.trans hE0, hclosed, hproper, hd, ?_⟩
  intro s hs
  let t : unitInterval := ⟨s.1 / r, div_nonneg s.2 hr.le, (div_le_one hr).mpr hs⟩
  have hclock : r * t.1 = s.1 := mul_div_cancel₀ _ hr.ne'
  have htime : (⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
      mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ : NNReal) = s := by
    apply Subtype.ext
    change (pointSmoothConformalEDist a y E.start E.finish).toReal * t.1 = s.1
    rw [hEL]
    exact hclock
  have hagree : γ s = E.curve t := by rw [← htime]; exact hseed t
  refine ⟨hagree.symm ▸ hEP t, ?_⟩
  rw [hagree, hEpolar t, mul_comm t.1 r, hclock]

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
