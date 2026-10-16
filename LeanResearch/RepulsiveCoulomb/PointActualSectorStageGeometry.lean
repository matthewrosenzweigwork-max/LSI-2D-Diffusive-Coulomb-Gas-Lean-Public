module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorEdgeInterior
public import LeanResearch.RepulsiveCoulomb.PointActualOpenDirectionUnmarked
public import LeanResearch.RepulsiveCoulomb.PointCappedSectorStageAtApex
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnPhysicalDirectionLink

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Collect only actual geometric data and proved
finite-direction inequalities, then derive arbitrary finite-stage regularity.
There is no sector map, continuation certificate, compatibility assertion, or
stage-flatness field in the input structure. The width may be instantiated by
the frozen first-marked minimum theorem; a smaller width also embeds.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

structure PointActualSectorData {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ha : ∀ j, 0 ≤ a j) (P : Set ℂ) where
  halfplane : ℂ ≃ₜ ℂ
  halfplane_eq : P = halfplane ⁻¹' planarClosedUpperHalfplane
  pieceCount : ℕ
  pieces : Fin pieceCount → PointClosedBoundaryGeodesicPiece a y
  boundary_cover : frontier P = ⋃ i, range (pieces i).curve
  nu : ℂ →₀ ℝ
  alpha : ℂ →₀ ℝ
  budget : PointSignedBudgetInvariant nu alpha
  boundary_atom : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
    nu p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (K.hi - K.lo)
  interior_support : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 →
    p ∈ pointSignedMarked nu alpha
  ray : NNReal → ℂ
  ray_metric : ∀ s t, (pointSmoothConformalEDist a y (ray s) (ray t)).toReal = dist s t
  ray_mem : ∀ t, ray t ∈ P
  ray_frontier : ∀ t, ray t ∈ frontier P
  ray_clean : Disjoint ((↑(pointSignedMarked nu alpha) : Set ℂ) \ {ray 0}) (range ray)
  chart : PointRetainedConeNeighborhood a y P (ray 0)
  admissible : chart.Admissible
  lowerRadius : ℝ
  lowerRadius_pos : 0 < lowerRadius
  lower_germ : ∀ t : NNReal, (t : ℝ) ≤ lowerRadius →
    chart.chart (ray t) = pointRadialSectorPoint t.1 chart.lo
  beta : ℝ
  beta_pos : 0 < beta
  beta_pi : beta ≤ Real.pi
  beta_width : beta ≤ chart.flatPhysicalWidth
  beta_budget : beta ≤ alpha (ray 0)
  markedEdge : {x : ℂ // x ∈ (pointSignedMarked nu alpha).erase (ray 0)} →
    PointGeodesicTreeEdge a y
  marked_start : ∀ i, (markedEdge i).start = ray 0
  marked_finish : ∀ i, (markedEdge i).finish = i.1
  marked_mem : ∀ i t, (markedEdge i).curve t ∈ P
  direction : {x : ℂ // x ∈ (pointSignedMarked nu alpha).erase (ray 0)} → ℝ
  direction_actual : ∀ i, direction i = chart.actualPhysicalDirection ha y admissible
    (markedEdge i) (pointRayComparisonEdge ha y ray ray_metric (markedEdge i))
    (marked_start i) rfl (marked_mem i) (fun u ↦ ray_mem _)
  beta_first : ∀ i, beta ≤ direction i

namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

def realRay : ℝ → ℂ := D.ray ∘ Real.toNNReal

theorem realRay_continuous : Continuous D.realRay :=
  (pointMetricRay_isClosedEmbedding ha y D.ray D.ray_metric).continuous.comp continuous_real_toNNReal

@[simp] theorem realRay_zero : D.realRay 0 = D.ray 0 := by
  simp [realRay]

theorem realRay_metric : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
    (pointSmoothConformalEDist a y (D.realRay s) (D.realRay t)).toReal = dist s t := by
  intro s hs t ht
  change (pointSmoothConformalEDist a y (D.ray s.toNNReal) (D.ray t.toNNReal)).toReal = _
  rw [D.ray_metric, NNReal.dist_eq, Real.coe_toNNReal s hs,
    Real.coe_toNNReal t ht, Real.dist_eq]

theorem realRay_frontier (s : ℝ) (_hs : s ∈ Ici (0 : ℝ)) :
    D.realRay s ∈ frontier P := D.ray_frontier _

theorem comparisonEdge_real_clock (E : PointGeodesicTreeEdge a y) (t : unitInterval) :
    (pointRayComparisonEdge ha y D.ray D.ray_metric E).curve t =
      D.realRay (pointActualEdgeLength (pointRayComparisonEdge ha y D.ray D.ray_metric E) * t.1) := by
  rw [pointRayComparisonEdge_length, pointRayComparisonEdge_curve]
  apply congrArg D.ray
  apply Subtype.ext
  exact (Real.coe_toNNReal _
    (mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1)).symm

theorem comparisonEdge_raw_lower (E : PointGeodesicTreeEdge a y) :
    D.chart.actualInitialRawAngle ha y D.admissible
      (pointRayComparisonEdge ha y D.ray D.ray_metric E) rfl (fun u ↦ D.ray_mem _) = D.chart.lo := by
  apply D.chart.reference_angle_eq_actual_clean_germ ha y D.admissible
    (pointRayComparisonEdge ha y D.ray D.ray_metric E) rfl (fun u ↦ D.ray_mem _)
    D.realRay (D.comparisonEdge_real_clock E) D.lowerRadius_pos
    ⟨le_rfl, D.chart.width_pos.le⟩
  intro u hu
  have hn : (u.toNNReal : ℝ) = u := Real.coe_toNNReal u hu.1.le
  have h := D.lower_germ u.toNNReal (by rw [hn]; exact hu.2.le)
  change D.chart.chart (D.ray u.toNNReal) = pointRadialSectorPoint (↑u.toNNReal) D.chart.lo at h
  change D.chart.chart (D.ray u.toNNReal) = pointRadialSectorPoint u D.chart.lo
  rwa [hn] at h

/-- Every nonapex point of a genuine seed-anchored finite convex stage in a
strict interior angular window is inside P and unmarked. Both geometric
exclusions are proved from the actual stage radial edge and true budget. -/
theorem stage_interior_unmarked
    {K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (hKsector : K ⊆ closedEuclideanSector D.beta)
    (hKarg : ∀ q : K, q.1 ≠ 0 → Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (hseed : ∀ z : K, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) :
    (f q).1 ∈ interior P ∧ (f q).1 ∉ pointSignedMarked D.nu D.alpha := by
  have hcenter : (f ⟨0, h0⟩).1 = D.ray 0 := by
    rw [hseed ⟨0, h0⟩ (by simpa only [norm_zero] using D.chart.radius_pos.le),
      D.chart.flatInverse_zero]
  let E := pointConvexRadialEdgeAt ha y hK h0 f hd hcenter q hq
  have hEP := pointConvexRadialEdgeAt_mem ha y hK h0 f hd hcenter q hq
  let F := pointRayComparisonEdge ha y D.ray D.ray_metric E
  have hFP : ∀ t, F.curve t ∈ P := fun _ ↦ D.ray_mem _
  obtain ⟨hraw, hdir⟩ := D.chart.actualPhysicalDirection_of_capped_seed_stage_at
    ha y hK h0 f hd hcenter D.admissible D.beta_width hKsector hseed q hq
      (hKarg q hq) F rfl hFP (D.comparisonEdge_raw_lower E)
  have hbudgetdir : D.chart.actualPhysicalDirection ha y D.admissible E F rfl rfl hEP hFP ≤
      D.alpha E.start := by
    rw [hdir]
    exact (hKarg q hq).2.le.trans D.beta_budget
  have hinterior := point_actual_sector_edge_positive_mem_interior ha y
    D.halfplane D.halfplane_eq D.pieces D.boundary_cover E F hEP rfl hFP
    D.chart D.admissible hraw D.realRay D.realRay_continuous D.realRay_zero
    D.realRay_metric D.realRay_frontier (D.comparisonEdge_real_clock E)
    D.budget D.boundary_atom hbudgetdir 1 (by norm_num)
  have hunmarked := point_actual_open_direction_edge_unmarked ha y D.ray D.ray_metric
    D.ray_mem D.chart D.admissible D.markedEdge D.marked_start D.marked_finish
    D.marked_mem D.direction D.direction_actual D.beta_first E rfl hEP
    (hdir.trans_lt (hKarg q hq).2) 1 (by norm_num)
  have hfinish : E.curve (1 : unitInterval) = (f q).1 := E.curve_finish
  simpa only [hfinish] using And.intro hinterior hunmarked

/-- Whole flat metric disks on every nonapex stage point are constructed from
actual interior membership and actual finite curvature support. -/
theorem stage_flatDisk
    {K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (hKsector : K ⊆ closedEuclideanSector D.beta)
    (hKarg : ∀ q : K, q.1 ≠ 0 → Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (hseed : ∀ z : K, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) :
    Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) (f q)) := by
  obtain ⟨hinterior, hunmarked⟩ := D.stage_interior_unmarked hK h0 hKsector hKarg f hd hseed q hq
  exact point_actual_unmarked_interior_flatDisk ha y D.interior_support hinterior hunmarked

end PointActualSectorData
end RepulsiveCoulomb
