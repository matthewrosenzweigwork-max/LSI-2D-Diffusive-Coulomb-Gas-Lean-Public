import LeanResearch.RepulsiveCoulomb.PointActualFirstSectorData
import LeanResearch.RepulsiveCoulomb.PointRegularOpenEdgeContinuation

/-! ISOLATED SOURCE-ONLY DRAFT. Identify first actual top-edge contact with
the closest finite-minimum marked endpoint. The completed top edge is never
identified with an arbitrarily chosen ambient continuation past that endpoint.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointGeodesicEdgeRebase {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (E : PointGeodesicTreeEdge a y) {p : ℂ} (hp : E.start = p) : PointGeodesicTreeEdge a y where
  start := p
  finish := E.finish
  distinct := by rw [← hp]; exact E.distinct
  curve := E.curve
  curve_start := E.curve_start.trans hp
  curve_finish := E.curve_finish
  continuous := E.continuous
  geodesic := by rw [← hp]; exact E.geodesic

namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

theorem initial_cap_le_width : min Real.pi (D.alpha (D.ray 0)) ≤ D.chart.flatPhysicalWidth := by
  obtain ⟨A, hA⟩ := D.boundary_atom (D.ray 0) (D.ray_frontier 0)
  have hwidth := D.chart.physical_width_eq A
  have hν : D.nu (D.ray 0) = Real.pi - D.chart.flatPhysicalWidth := by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hA, hwidth]
  exact D.budget.min_pi_budget_le_boundary_angle (D.ray 0) hν

/-- For the actually closest beta-direction marked endpoint, the closed
sector's top edge reaches that SAME point at its actual distance. Every
strictly earlier positive point of the top edge is unmarked. -/
theorem completed_map_first_marked_top
    (F : closedEuclideanSector D.beta → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hseed : ∀ z, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1)
    (hcap : D.beta < min Real.pi (D.alpha (D.ray 0)))
    (i : {x : ℂ // x ∈ (pointSignedMarked D.nu D.alpha).erase (D.ray 0)})
    (hi : D.direction i = D.beta)
    (hbefore : ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
      (D.markedEdge i).curve t ∉ pointSignedMarked D.nu D.alpha) :
    ∃ L : ℝ, 0 < L ∧
      ∃ q : closedEuclideanSector D.beta, q.1 = sectorPolar L D.beta ∧ (F q).1 = i.1 ∧
        ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
          ∀ qt : closedEuclideanSector D.beta, qt.1 = sectorPolar (L * t.1) D.beta →
            (F qt).1 ∉ pointSignedMarked D.nu D.alpha := by
  let M := pointGeodesicEdgeRebase (D.markedEdge i) (D.marked_start i)
  have hMP : ∀ t, M.curve t ∈ P := D.marked_mem i
  let G := pointRayComparisonEdge ha y D.ray D.ray_metric M
  have hGP : ∀ t, G.curve t ∈ P := fun _ ↦ D.ray_mem _
  have hdirM : D.chart.actualPhysicalDirection ha y D.admissible M G rfl rfl hMP hGP = D.beta := by
    have h := D.chart.actualPhysicalDirection_of_endpoint_on_edge ha y D.ray D.ray_metric D.ray_mem
      D.admissible (D.markedEdge i) M (D.marked_start i) rfl (D.marked_mem i) hMP
      (t := 1) (by norm_num) (D.markedEdge i).curve_finish.symm
    exact h.trans ((D.direction_actual i).symm.trans hi)
  have hrawmem := (D.chart.actualInitialRawAngle_spec ha y D.admissible M rfl hMP).1
  let A := coalescedPointExponent a y (D.ray 0) / 2 + 1
  have hA : 0 < A := by dsimp [A]; linarith [coalescedPointExponent_nonneg a y (D.ray 0)]
  have hphysical : A * |D.chart.actualInitialRawAngle ha y D.admissible M rfl hMP - D.chart.lo| = D.beta := by
    have h := hdirM
    unfold PointRetainedConeNeighborhood.actualPhysicalDirection at h
    rwa [D.comparisonEdge_raw_lower M] at h
  have hwidth : D.beta < D.chart.flatPhysicalWidth := hcap.trans_le D.initial_cap_le_width
  have hrawopen : D.chart.actualInitialRawAngle ha y D.admissible M rfl hMP ∈ Ioo D.chart.lo D.chart.hi := by
    apply sectorReturn_raw_direction_interior_of_physical_bounds hA hrawmem (Or.inl rfl)
    · rw [hphysical]
      exact D.beta_pos
    · rw [hphysical]
      exact hwidth
  have hMint := point_actual_sector_edge_positive_mem_interior ha y D.halfplane D.halfplane_eq
    D.pieces D.boundary_cover M G hMP rfl hGP D.chart D.admissible hrawopen
    D.realRay D.realRay_continuous D.realRay_zero D.realRay_metric D.realRay_frontier
    (D.comparisonEdge_real_clock M) D.budget D.boundary_atom
    (hdirM.trans_le D.beta_budget)
  have hregular : ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) ⟨M.curve t, hMP t⟩) := by
    intro t ht ht1
    exact point_actual_unmarked_interior_flatDisk ha y D.interior_support (hMint t ht) (hbefore t ht ht1)
  let L := pointActualEdgeLength M
  have hL : 0 < L := pointActualEdgeLength_pos ha y M
  have htop : sectorPolar L D.beta ∈ closedEuclideanSector D.beta := by
    change 0 ≤ Complex.arg (sectorPolar L D.beta) ∧ Complex.arg (sectorPolar L D.beta) ≤ D.beta
    rw [sectorPolar_arg hL ⟨by linarith [D.beta_pos, Real.pi_pos], D.beta_pi⟩]
    exact ⟨D.beta_pos.le, le_rfl⟩
  let q : closedEuclideanSector D.beta := ⟨sectorPolar L D.beta, htop⟩
  have hq : q.1 ≠ 0 := by
    intro he
    change sectorPolar L D.beta = 0 at he
    have hn := sectorPolar_norm hL.le D.beta
    rw [he, norm_zero] at hn
    exact hL.ne' hn.symm
  have h0 : (0 : ℂ) ∈ closedEuclideanSector D.beta := by
    simp [closedEuclideanSector, D.beta_pos.le]
  have hcenter : (F ⟨0, h0⟩).1 = D.ray 0 := by
    rw [hseed ⟨0, h0⟩ (by simpa only [norm_zero] using D.chart.radius_pos.le), D.chart.flatInverse_zero]
  let hconv := closedEuclideanSector_convex D.beta_pos D.beta_pi
  let E := pointConvexRadialEdgeAt ha y hconv h0 F hd hcenter q hq
  have hEP := pointConvexRadialEdgeAt_mem ha y hconv h0 F hd hcenter q hq
  have hrawE : D.chart.actualInitialRawAngle ha y D.admissible E rfl hEP =
      D.chart.lo + A⁻¹ * D.beta := by
    have h := D.chart.actualRawAngle_of_capped_seed_stage_at ha y hconv h0 F hd hcenter
      D.admissible D.beta_width subset_rfl hseed q hq
    simpa only [q, sectorPolar_arg hL ⟨by linarith [D.beta_pos, Real.pi_pos], D.beta_pi⟩] using h
  have hrawM : D.chart.actualInitialRawAngle ha y D.admissible M rfl hMP =
      D.chart.lo + A⁻¹ * D.beta := by
    rw [abs_of_nonneg (sub_nonneg.mpr hrawmem.1)] at hphysical
    have h := congrArg (fun r : ℝ ↦ A⁻¹ * r) hphysical
    rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] at h
    linarith
  have hlength : pointActualEdgeLength E = L := by
    change (pointSmoothConformalEDist a y (D.ray 0) (F q).1).toReal = L
    rw [← hcenter, hd]
    change dist (0 : ℂ) (sectorPolar L D.beta) = L
    rw [dist_zero_left, sectorPolar_norm hL.le]
  have hoverlap := D.chart.actual_edges_overlap_of_initial_angle_eq ha y D.admissible
    E M rfl rfl hEP hMP hlength (hrawE.trans hrawM.symm)
  have heq := pointActualEdges_eq_of_initial_overlap_full_flat_open ha y E M hEP hMP rfl hlength hregular hoverlap
  have hend : (F q).1 = i.1 := by
    have h := congrFun heq (⟨1, by norm_num⟩ : unitInterval)
    rw [E.curve_finish, M.curve_finish] at h
    exact h.trans (D.marked_finish i)
  refine ⟨L, hL, q, rfl, hend, ?_⟩
  intro t ht ht1 qt hqt
  let z := convexDomainSegment hconv ⟨0, h0⟩ q t
  have hz : z = qt := by
    apply Subtype.ext
    rw [convexDomainSegment_from_zero_val hconv h0 q t, hqt]
    change t.1 • sectorPolar L D.beta = sectorPolar (L * t.1) D.beta
    simp only [sectorPolar, Complex.real_smul, Complex.ofReal_mul]
    ring
  have h := congrFun heq t
  change (F z).1 = M.curve t at h
  rw [hz] at h
  exact h.symm ▸ hbefore t ht ht1

end PointActualSectorData
end RepulsiveCoulomb
