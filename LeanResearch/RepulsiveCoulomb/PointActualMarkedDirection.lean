module

public import LeanResearch.RepulsiveCoulomb.PointCleanBoundaryContinuation
public import LeanResearch.RepulsiveCoulomb.PointRetainedFrontierEndpoint
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments

@[expose] public section

/-! ISOLATED SOURCE-ONLY INTEGRATION. No compiler or canonical staging.
The local frontier theorem is the immutable outside sector-worker companion.
Actual minimizing edges, sampled germs, and angle selectors are constructed.
Only actual point-region geometry and a literal clean metric boundary ray are
inputs. No angular selector or positivity certificate is an input. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb
namespace PointRetainedConeNeighborhood

/-- Strengthen the constructed canonical germ specification by retaining its
actual sample distance. This follows from its construction and uniqueness. -/
theorem actualInitialRawAngle_sample
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) :
    ∃ r : ℝ, ∃ τ : unitInterval,
      0 < r ∧ r < C.radius ∧ 0 < τ.1 ∧ τ.1 < 1 ∧
      (pointSmoothConformalEDist a y (E.curve τ) p).toReal = r ∧
      ∀ u : unitInterval,
        C.chart (E.curve (pointEdgeSubparam 0 τ u)) =
          pointRadialSectorPoint (u.1 * r)
            (C.actualInitialRawAngle ha y hadm E hstart hP) := by
  obtain ⟨r, τ, θ, hr, hrR, hτ, hτ1, hθ, hd, hrad⟩ :=
    C.exists_actual_edge_initial_raw_angle ha y hadm E hstart hP
  obtain ⟨hκ, s, σ, hs, _, hσ, _, hrad'⟩ :=
    C.actualInitialRawAngle_spec ha y hadm E hstart hP
  have he := C.actual_initial_raw_angle_unique hadm E
    hr hs hτ hσ hθ hκ hrad hrad'
  exact ⟨r, τ, hr, hrR, hτ, hτ1, hd, by simpa only [he] using hrad⟩

/-- The constructed raw germ of an actual frontier edge is one of the two
full retained endpoints. The endpoint is concluded from actual frontier
membership and the genuine chart; it is not supplied by the caller. -/
theorem actualInitialRawAngle_frontier_endpoint
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P)
    (hfront : ∀ t : unitInterval, 0 < t.1 → E.curve t ∈ frontier P) :
    C.actualInitialRawAngle ha y hadm E hstart hP = C.lo ∨
      C.actualInitialRawAngle ha y hadm E hstart hP = C.hi := by
  obtain ⟨r, τ, hr, hrR, hτ, _, hd, hrad⟩ :=
    C.actualInitialRawAngle_sample ha y hadm E hstart hP
  have hchart := hrad 1
  have hlast : pointEdgeSubparam (0 : unitInterval) τ (1 : unitInterval) = τ :=
    pointEdgeSubparam_one 0 τ
  rw [hlast] at hchart
  simp only [Set.Icc.coe_one, one_mul] at hchart
  exact C.frontier_radial_coordinate_endpoint (hfront τ hτ)
    (hd.trans_lt hrR) hr
    (C.actualInitialRawAngle_spec ha y hadm E hstart hP).1 hchart

/-- Equal constructed raw angles of equal-speed actual edges give a positive
actual overlap. Product sample clocks give the common physical radius. -/
theorem actual_edges_overlap_of_initial_angle_eq
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    (hangle : C.actualInitialRawAngle ha y hadm E hE0 hEP =
      C.actualInitialRawAngle ha y hadm F hF0 hFP) :
    ∃ t : unitInterval, 0 < t.1 ∧ E.curve t = F.curve t := by
  obtain ⟨r, τ, hr, hrR, hτ, _, hdr, hrad⟩ :=
    C.actualInitialRawAngle_sample ha y hadm E hE0 hEP
  obtain ⟨s, σ, hs, hsR, hσ, _, hds, hsrad⟩ :=
    C.actualInitialRawAngle_sample ha y hadm F hF0 hFP
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos
    (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  have h0E : E.curve 0 = p := E.curve_start.trans hE0
  have h0F : F.curve 0 = p := F.curve_start.trans hF0
  have hrclock : r = τ.1 * L := by
    have h := E.geodesic τ 0
    rw [h0E, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg τ.2.1, hdr] at h
    exact h
  have hsclock : s = σ.1 * L := by
    have h := F.geodesic σ 0
    rw [h0F, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg σ.2.1, hds, ← hspeed] at h
    exact h
  let t := pointEdgeSubparam 0 τ σ
  have htval : t.1 = σ.1 * τ.1 := by
    simp [t, pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
  have hparam : t = pointEdgeSubparam 0 σ τ := by
    apply Subtype.ext
    simp only [t, pointEdgeSubparam, AffineMap.lineMap_apply_module',
      Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
    ring
  have hechart : C.chart (E.curve t) = C.chart (F.curve t) := by
    calc
      C.chart (E.curve t) = pointRadialSectorPoint (σ.1 * r)
          (C.actualInitialRawAngle ha y hadm E hE0 hEP) := hrad σ
      _ = pointRadialSectorPoint (τ.1 * s)
          (C.actualInitialRawAngle ha y hadm F hF0 hFP) := by
        rw [hangle, hrclock, hsclock]
        congr 1
        ring
      _ = C.chart (F.curve t) := by
        rw [hparam]
        exact (hsrad τ).symm
  have hEr : (pointSmoothConformalEDist a y (E.curve t) p).toReal ≤ C.radius := by
    have h := E.geodesic t 0
    rw [h0E, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h, htval]
    change σ.1 * τ.1 * L ≤ C.radius
    calc
      σ.1 * τ.1 * L = σ.1 * r := by rw [hrclock]; ring
      _ ≤ r := mul_le_of_le_one_left hr.le σ.2.2
      _ ≤ C.radius := hrR.le
  have hFr : (pointSmoothConformalEDist a y (F.curve t) p).toReal ≤ C.radius := by
    have h := F.geodesic t 0
    rw [h0F, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1, ← hspeed] at h
    rw [h, htval]
    change σ.1 * τ.1 * L ≤ C.radius
    calc
      σ.1 * τ.1 * L = τ.1 * s := by rw [hsclock]; ring
      _ ≤ s := mul_le_of_le_one_left hs.le τ.2.2
      _ ≤ C.radius := hsR.le
  exact ⟨t, by rw [htval]; exact mul_pos hσ hτ,
    C.chart.injOn (C.source hEr) (C.source hFr) hechart⟩

/-- The full physical interval coordinate between two actual initial germs.
For an actual boundary reference edge, the endpoint theorem below identifies
this as one of the two ordinary oriented interval formulas. -/
def actualPhysicalDirection
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P) : ℝ :=
  (coalescedPointExponent a y p / 2 + 1) *
    |C.actualInitialRawAngle ha y hadm E hE0 hEP -
      C.actualInitialRawAngle ha y hadm F hF0 hFP|

theorem actualPhysicalDirection_endpoint_formula
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P)
    (hfront : ∀ t : unitInterval, 0 < t.1 → F.curve t ∈ frontier P) :
    (C.actualInitialRawAngle ha y hadm F hF0 hFP = C.lo ∧
      C.actualPhysicalDirection ha y hadm E F hE0 hF0 hEP hFP =
        (coalescedPointExponent a y p / 2 + 1) *
          (C.actualInitialRawAngle ha y hadm E hE0 hEP - C.lo)) ∨
    (C.actualInitialRawAngle ha y hadm F hF0 hFP = C.hi ∧
      C.actualPhysicalDirection ha y hadm E F hE0 hF0 hEP hFP =
        (coalescedPointExponent a y p / 2 + 1) *
          (C.hi - C.actualInitialRawAngle ha y hadm E hE0 hEP)) := by
  have hθ := (C.actualInitialRawAngle_spec ha y hadm E hE0 hEP).1
  rcases C.actualInitialRawAngle_frontier_endpoint ha y hadm F hF0 hFP hfront with h | h
  · exact Or.inl ⟨h, by
      unfold actualPhysicalDirection
      rw [h, abs_of_nonneg (sub_nonneg.mpr hθ.1)]⟩
  · exact Or.inr ⟨h, by
      unfold actualPhysicalDirection
      rw [h, abs_of_nonpos (sub_nonpos.mpr hθ.2), neg_sub]⟩

theorem actualPhysicalDirection_mem
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P) :
    C.actualPhysicalDirection ha y hadm E F hE0 hF0 hEP hFP ∈
      Icc (0 : ℝ) C.flatPhysicalWidth := by
  have hA : 0 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  have hθ := (C.actualInitialRawAngle_spec ha y hadm E hE0 hEP).1
  have hφ := (C.actualInitialRawAngle_spec ha y hadm F hF0 hFP).1
  refine ⟨mul_nonneg hA (abs_nonneg _), ?_⟩
  apply mul_le_mul_of_nonneg_left _ hA
  apply abs_le.mpr
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

/-- Strict positivity is derived from actual geometry. Zero angle constructs
an overlap; genuine flat charts propagate it; the supplied actual endpoints
then contradict cleanliness. -/
theorem actualPhysicalDirection_pos_of_clean_flat_reference
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P)
    (hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal)
    (hflat : ∀ t : unitInterval, 0 < t.1 →
      ∃ D : PointRetainedConeNeighborhood a y P (F.curve t),
        D.flatPhysicalWidth ≤ Real.pi)
    (hfinish : E.finish ≠ F.finish) :
    0 < C.actualPhysicalDirection ha y hadm E F hE0 hF0 hEP hFP := by
  have hA : 0 < coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  apply mul_pos hA
  apply abs_pos.mpr
  intro he
  have hangle := sub_eq_zero.mp he
  have hoverlap := C.actual_edges_overlap_of_initial_angle_eq ha y hadm
    E F hE0 hF0 hEP hFP hspeed hangle
  have hcurves := pointActualEdges_eq_of_initial_overlap_flat ha y E F
    hEP hFP (hE0.trans hF0.symm) hspeed hflat hoverlap
  apply hfinish
  exact E.curve_finish.symm.trans ((congrFun hcurves 1).trans F.curve_finish)

end PointRetainedConeNeighborhood

/-- Actual endpoint distance; this is not a new metric or a prescribed clock. -/
def pointActualEdgeLength {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (E : PointGeodesicTreeEdge a y) : ℝ :=
  (pointSmoothConformalEDist a y E.start E.finish).toReal

theorem pointActualEdgeLength_pos {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    0 < pointActualEdgeLength E :=
  ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne

/-- The literal clean-ray prefix having the same ACTUAL metric length as E. -/
def pointRayComparisonEdge {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E : PointGeodesicTreeEdge a y) : PointGeodesicTreeEdge a y :=
  pointMetricRaySegment ha y ρ hρ ⟨pointActualEdgeLength E, (pointActualEdgeLength_pos ha y E).le⟩
    (pointActualEdgeLength_pos ha y E)

@[simp] theorem pointRayComparisonEdge_start {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E : PointGeodesicTreeEdge a y) : (pointRayComparisonEdge ha y ρ hρ E).start = ρ 0 := rfl

@[simp] theorem pointRayComparisonEdge_finish {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E : PointGeodesicTreeEdge a y) : (pointRayComparisonEdge ha y ρ hρ E).finish =
      ρ ⟨pointActualEdgeLength E, (pointActualEdgeLength_pos ha y E).le⟩ := rfl

@[simp] theorem pointRayComparisonEdge_curve {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E : PointGeodesicTreeEdge a y) (t : unitInterval) :
    (pointRayComparisonEdge ha y ρ hρ E).curve t =
      ρ ⟨pointActualEdgeLength E * t.1,
        mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1⟩ := rfl

theorem pointRayComparisonEdge_length {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E : PointGeodesicTreeEdge a y) :
    pointActualEdgeLength (pointRayComparisonEdge ha y ρ hρ E) = pointActualEdgeLength E := by
  change (pointSmoothConformalEDist a y (ρ 0)
    (ρ (NNReal.mk (pointActualEdgeLength E) (pointActualEdgeLength_pos ha y E).le))).toReal = _
  rw [hρ, NNReal.dist_eq, NNReal.coe_zero, NNReal.coe_mk, zero_sub, abs_neg,
    abs_of_nonneg (pointActualEdgeLength_pos ha y E).le]

/-- Actual cleanliness excludes every positive point of the metric ray from
its finite marked set, including any budget-only marks. -/
theorem pointMetricRay_positive_not_marked
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    {S : Set ℂ} (hclean : Disjoint (S \ {ρ 0}) (range ρ))
    (t : NNReal) (ht : 0 < t) : ρ t ∉ S := by
  have hne : ρ t ≠ ρ 0 := by
    intro he
    have hd := hρ t 0
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero,
      NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)] at hd
    exact (ne_of_gt ht) (Subtype.ext hd.symm)
  intro hm
  exact disjoint_left.mp hclean ⟨hm, hne⟩ (mem_range_self t)

/-- Strict positive direction for an actual marked endpoint, against its
literal clean-ray comparison edge. Flatness is DERIVED from the actual marked
set and residual boundary atom identity, using the genuine retained charts. -/
theorem PointRetainedConeNeighborhood.actual_marked_direction_pos
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    {ν α : ℂ →₀ ℝ}
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hboundary : ∀ t : NNReal, 0 < t →
      ∃ D : PointRetainedConeNeighborhood a y P (ρ t),
        ν (ρ t) = Real.pi - D.flatPhysicalWidth)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start = ρ 0)
    (hEP : ∀ t, E.curve t ∈ P)
    (hmark : E.finish ∈ pointSignedMarked ν α) :
    0 < C.actualPhysicalDirection ha y hadm E (pointRayComparisonEdge ha y ρ hρ E)
      hE0 rfl hEP (fun t ↦ hρP _) := by
  let F := pointRayComparisonEdge ha y ρ hρ E
  have hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y F.start F.finish).toReal :=
    (pointRayComparisonEdge_length ha y ρ hρ E).symm
  have hflat : ∀ t : unitInterval, 0 < t.1 →
      ∃ D : PointRetainedConeNeighborhood a y P (F.curve t),
        D.flatPhysicalWidth ≤ Real.pi := by
    intro t ht
    let u : NNReal := ⟨pointActualEdgeLength E * t.1,
      mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1⟩
    have hu : 0 < u := mul_pos (pointActualEdgeLength_pos ha y E) ht
    have hoff := pointMetricRay_positive_not_marked y ρ hρ hclean u hu
    obtain ⟨D, hD⟩ := hboundary u hu
    exact ⟨D, (pointSigned_clean_boundary_physical_width_pi D hoff hD).le⟩
  have hfinish : E.finish ≠ F.finish := by
    intro he
    have hn := pointMetricRay_positive_not_marked y ρ hρ hclean
      ⟨pointActualEdgeLength E, (pointActualEdgeLength_pos ha y E).le⟩
      (pointActualEdgeLength_pos ha y E)
    apply hn
    change F.finish ∈ pointSignedMarked ν α
    exact he ▸ hmark
  exact C.actualPhysicalDirection_pos_of_clean_flat_reference ha y hadm E F
    hE0 rfl hEP (fun t ↦ hρP _) hspeed hflat hfinish

end RepulsiveCoulomb
