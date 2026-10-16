module

public import LeanResearch.RepulsiveCoulomb.PointRetainedFullFlatDiskChart
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk

@[expose] public section

/-! Genuine full Euclidean charts at actual interior zero-exponent points.
The metric radius is chosen inside P using its literal interior, then the
existing ambient cone-disk theorem constructs the entire ball equivalence.
No retained-full-chart hypothesis or continuation certificate is required. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem exists_pointInterior_zeroExponent_flatDiskChart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (hp : p ∈ interior P)
    (hzero : coalescedPointExponent a y p = 0) :
    Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
      ⟨p, interior_subset hp⟩) := by
  have hball : ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      (pointSmoothConformalEDist a y z p).toReal < ε → z ∈ P := by
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    letI : PseudoMetricSpace ℂ := (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    letI : PseudoEMetricSpace ℂ := (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace
    letI : UniformSpace ℂ := (pointSmoothConformalMetricSpace ha y).toUniformSpace
    letI : TopologicalSpace ℂ := (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    have hp' : p ∈ interior P := by
      change p ∈ @interior ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P
      rw [pointSmoothConformalMetricSpace_topology ha y]
      exact hp
    obtain ⟨ε, hε, hεP⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp')
    exact ⟨ε, hε, fun z hz ↦ hεP hz⟩
  obtain ⟨ε, hε, hεP⟩ := hball
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y p
  let R := min C.radius ε
  have hR : 0 < R := lt_min C.radius_pos hε
  have hRC : R ≤ C.radius := min_le_left _ _
  have hRε : R ≤ ε := min_le_right _ _
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  letI : EMetricSpace P := (pointRegionMetricSpace ha y P).toEMetricSpace
  letI : PseudoMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
  let pP : P := ⟨p, interior_subset hp⟩
  have hsrc (z : ball pP R) :
      (pointSmoothConformalEDist a y z.1.1 p).toReal ≤ C.radius := z.2.le.trans hRC
  have hcoord (z : ball pP R) : C.chart z.1.1 ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, C.norm_chart (hsrc z)]
    exact z.2
  let F : ball pP R → ball (0 : ℂ) R := fun z ↦ ⟨C.chart z.1.1, hcoord z⟩
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (C.chart z.1.1) (C.chart w.1.1) =
      (pointSmoothConformalEDist a y z.1.1 w.1.1).toReal
    rw [C.metric _ (hsrc z) _ (hsrc w), pointClassicalConeDist_eq_euclidean_of_zero y hzero]
  have hsurj : Function.Surjective F := by
    intro w
    have hwR : ‖w.1‖ < R := by simpa only [mem_ball, dist_zero_right] using w.2
    obtain ⟨z, hz, hzw⟩ := C.onto.surjOn (hwR.le.trans hRC)
    have hzR : (pointSmoothConformalEDist a y z p).toReal < R := by
      rw [← C.norm_chart hz, hzw]
      exact hwR
    have hzP : z ∈ P := hεP z (hzR.trans_le hRε)
    refine ⟨⟨⟨z, hzP⟩, hzR⟩, ?_⟩
    exact Subtype.ext hzw
  let e : ball pP R ≃ᵢ ball (0 : ℂ) R :=
    { Equiv.ofBijective F ⟨hF.injective, hsurj⟩ with isometry_toFun := hF }
  exact ⟨⟨R, hR, e, C.center⟩⟩

end RepulsiveCoulomb
