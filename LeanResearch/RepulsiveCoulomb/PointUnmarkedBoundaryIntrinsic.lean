module

public import LeanResearch.RepulsiveCoulomb.PointUnmarkedBoundaryLocal

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Construct the actual constrained boundary length
metric and its minimizers; local flat-diameter chords then identify those
minimizers with actual ambient minimizing curves. -/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Genuine flat retained charts construct the center-to-nearby-point paths
needed by the existing intrinsic metric existence machinery. -/
theorem pointBoundaryFlat_radialPaths
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P)
    (hflat : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.flatPhysicalWidth = Real.pi) :
    @MetricRegionRadialPaths ℂ (pointSmoothConformalMetricSpace ha y) (frontier P) := by
  intro p hp
  obtain ⟨C, hC⟩ := hflat p hp
  refine ⟨C.radius, C.radius_pos, ?_⟩
  intro z hz hzp
  have hself : (pointSmoothConformalEDist a y p p).toReal < C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos
  obtain ⟨η, h0, h1, hc, hfront, hd⟩ :=
    C.boundaryFlat_exists_chord ha y hP hp hC hp hz hself hzp
  let γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = η ⟨t, ht⟩ :=
    IccExtend_of_mem _ _ ht
  have hγ0 : γ 0 = p := (hγ 0 (by norm_num)).trans h0
  have hγ1 : γ 1 = z := (hγ 1 (by norm_num)).trans h1
  have hγc : Continuous γ := continuous_IccExtend_iff.mpr hc
  have hc' : @Continuous ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  let Γ : @MetricRegionLengthPath ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (frontier P) p z :=
    @MetricRegionLengthPath.mk ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (frontier P) p z γ hc' hγ0 hγ1
      (fun t ht ↦ (hγ t ht).symm ▸ hfront ⟨t, ht⟩)
  refine ⟨Γ, ?_⟩
  change pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y p z
  rw [← hγ0, ← hγ1]
  apply pointConformalMetricLength_of_geodesic ha y
  intro s hs t ht
  rw [hγ0, hγ1, hγ s hs, hγ t ht]
  exact hd ⟨s, hs⟩ ⟨t, ht⟩

/-- Local equality follows from constructed literal boundary chords, rather
than from an assumed ambient-convexity or complete-boundary-line certificate. -/
theorem pointBoundaryFlat_intrinsic_pair_eq
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {p x z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hp : p ∈ frontier P) (hC : C.flatPhysicalWidth = Real.pi)
    (hx : x ∈ frontier P) (hz : z ∈ frontier P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal < C.radius)
    (hzR : (pointSmoothConformalEDist a y z p).toReal < C.radius) :
    @metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) (frontier P) x z =
      pointSmoothConformalEDist a y x z := by
  obtain ⟨γ, h0, h1, hc, hfront, hd⟩ :=
    C.boundaryFlat_exists_chord ha y hP hp hC hx hz hxR hzR
  rw [← pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
  exact pointRegionIntrinsicEDist_eq_of_contained_geodesic ha y γ h0 h1 hc hfront hd

/-- Closedness, connectedness, and genuine flat retained boundary charts
construct actual ambient minimizers contained entirely in the frontier. -/
theorem pointBoundaryFlat_geodesicallyConvex
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) (hconn : IsPreconnected (frontier P))
    (hflat : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.flatPhysicalWidth = Real.pi) :
    PointGeodesicallyConvex a y (frontier P) := by
  have hclosed' : @IsClosed ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (frontier P) := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact isClosed_frontier
  have hconn' : @IsPreconnected ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (frontier P) := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hradial := pointBoundaryFlat_radialPaths ha y hP hflat
  intro x hx z hz
  obtain ⟨η, h0, h1, hc, hd⟩ := @exists_metricRegionIntrinsic_geodesic ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
    (frontier P) hclosed' hconn' hradial ⟨x, hx⟩ ⟨z, hz⟩
  have hc' : Continuous η := by
    change @Continuous unitInterval (frontier P) _
      (pointRegionMetricSpace ha y (frontier P)).toUniformSpace.toTopologicalSpace η at hc
    rwa [pointRegionMetricSpace_topology ha y (frontier P)] at hc
  let γ : unitInterval → ℂ := fun t ↦ (η t).1
  have hγ0 : γ 0 = x := congrArg Subtype.val h0
  have hγ1 : γ 1 = z := congrArg Subtype.val h1
  have hγc : Continuous γ := continuous_subtype_val.comp hc'
  let L := (@metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y)
    (frontier P) x z).toReal
  have hlocal : ∀ t, ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ u ∈ U,
        (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = L * |u.1 - s.1| := by
    intro t
    obtain ⟨C, hC⟩ := hflat (γ t) (η t).2
    let U : Set unitInterval := {s | (pointSmoothConformalEDist a y (γ s) (γ t)).toReal < C.radius}
    have hγc' : @Continuous unitInterval ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
      rwa [pointSmoothConformalMetricSpace_topology ha y]
    have hU : IsOpen U := @IsOpen.preimage unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ hγc' _
      (@Metric.isOpen_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
        (γ t) C.radius)
    have ht : t ∈ U := by
      change (pointSmoothConformalEDist a y (γ t) (γ t)).toReal < C.radius
      rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
      exact C.radius_pos
    refine ⟨U, hU, ht, ?_⟩
    intro s hs u hu
    have he := pointBoundaryFlat_intrinsic_pair_eq ha y hP C (η t).2 hC
      (η s).2 (η u).2 hs hu
    rw [← he]
    exact (hd s u).trans (mul_comm _ _)
  have hglobal := pointConformal_local_geodesic_global ha y γ hlocal
  have hL : (pointSmoothConformalEDist a y x z).toReal = L := by
    have h := hglobal 0 1
    rw [hγ0, hγ1] at h
    simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero, abs_one, mul_one] using h
  exact ⟨γ, hγ0, hγ1, hγc, fun t ↦ (η t).2, fun s t ↦ by
    rw [hglobal s t, hL, mul_comm]⟩

end RepulsiveCoulomb
