module

public import LeanResearch.RepulsiveCoulomb.PointUnmarkedBoundaryIntrinsic
public import LeanResearch.RepulsiveCoulomb.ProperBoundaryEndClockArclength

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. A compact boundary-clock arc containing only
retained-width-pi points is ambient minimizing. No ambient cone exponent is
set to zero. Flat chords are kept in the arc by order, not by uniqueness. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- A local chord property, used only as an intermediate proved proposition. -/
def PointLocalMinimizingChords {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (Q : Set ℂ) : Prop :=
  ∀ p ∈ Q, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Q, ∀ z ∈ Q,
    (pointSmoothConformalEDist a y x p).toReal < r →
    (pointSmoothConformalEDist a y z p).toReal < r →
    ∃ γ : unitInterval → ℂ, γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧
      (∀ t, γ t ∈ Q) ∧ ∀ s t,
        (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
          |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal

/-- Actual local chords provide the radial competitors for the constructed
constrained length metric. -/
theorem pointLocalMinimizingChords_radialPaths
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {Q : Set ℂ} (hloc : PointLocalMinimizingChords a y Q) :
    @MetricRegionRadialPaths ℂ (pointSmoothConformalMetricSpace ha y) Q := by
  intro p hp
  obtain ⟨r, hr, hchord⟩ := hloc p hp
  refine ⟨r, hr, ?_⟩
  intro z hz hzp
  have hself : (pointSmoothConformalEDist a y p p).toReal < r := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hr
  obtain ⟨η, h0, h1, hc, hQ, hd⟩ := hchord p hp z hz hself hzp
  let γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = η ⟨t, ht⟩ :=
    IccExtend_of_mem _ _ ht
  have hγ0 : γ 0 = p := (hγ 0 (by norm_num)).trans h0
  have hγ1 : γ 1 = z := (hγ 1 (by norm_num)).trans h1
  have hγc : Continuous γ := continuous_IccExtend_iff.mpr hc
  have hc' : @Continuous ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  let Γ := @MetricRegionLengthPath.mk ℂ
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    Q p z γ hc' hγ0 hγ1 (fun t ht ↦ (hγ t ht).symm ▸ hQ ⟨t, ht⟩)
  refine ⟨Γ, ?_⟩
  change pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y p z
  rw [← hγ0, ← hγ1]
  apply pointConformalMetricLength_of_geodesic ha y
  intro s hs t ht
  rw [hγ0, hγ1, hγ s hs, hγ t ht]
  exact hd ⟨s, hs⟩ ⟨t, ht⟩

/-- Closed connected subsets with actual local ambient chords are convex.
The proof first constructs intrinsic minimizers, then applies ambient
local-to-global. This is not an assumed local-to-global certificate. -/
theorem pointGeodesicallyConvex_of_localMinimizingChords
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {Q : Set ℂ} (hclosed : IsClosed Q) (hconn : IsPreconnected Q)
    (hloc : PointLocalMinimizingChords a y Q) : PointGeodesicallyConvex a y Q := by
  have hclosed' : @IsClosed ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace Q := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hconn' : @IsPreconnected ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace Q := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hradial := pointLocalMinimizingChords_radialPaths ha y hloc
  intro x hx z hz
  obtain ⟨η, h0, h1, hc, hd⟩ := @exists_metricRegionIntrinsic_geodesic ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
    Q hclosed' hconn' hradial ⟨x, hx⟩ ⟨z, hz⟩
  have hc' : Continuous η := by
    change @Continuous unitInterval Q _
      (pointRegionMetricSpace ha y Q).toUniformSpace.toTopologicalSpace η at hc
    rwa [pointRegionMetricSpace_topology ha y Q] at hc
  let γ : unitInterval → ℂ := fun t ↦ (η t).1
  have hγ0 : γ 0 = x := congrArg Subtype.val h0
  have hγ1 : γ 1 = z := congrArg Subtype.val h1
  have hγc : Continuous γ := continuous_subtype_val.comp hc'
  let L := (@metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) Q x z).toReal
  have hlocal : ∀ t, ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ u ∈ U,
        (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = L * |u.1 - s.1| := by
    intro t
    obtain ⟨r, hr, hchord⟩ := hloc (γ t) (η t).2
    let U : Set unitInterval := {s | (pointSmoothConformalEDist a y (γ s) (γ t)).toReal < r}
    have hγc' : @Continuous unitInterval ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
      rwa [pointSmoothConformalMetricSpace_topology ha y]
    have hU : IsOpen U := @IsOpen.preimage unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ hγc' _
      (@Metric.isOpen_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace (γ t) r)
    have ht : t ∈ U := by
      change (pointSmoothConformalEDist a y (γ t) (γ t)).toReal < r
      rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
      exact hr
    refine ⟨U, hU, ht, ?_⟩
    intro s hs u hu
    obtain ⟨σ, hσ0, hσ1, hσc, hσQ, hσd⟩ :=
      hchord (γ s) (η s).2 (γ u) (η u).2 hs hu
    have he := pointRegionIntrinsicEDist_eq_of_contained_geodesic
      ha y σ hσ0 hσ1 hσc hσQ hσd
    rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y] at he
    rw [← he]
    exact (hd s u).trans (mul_comm _ _)
  have hglobal := pointConformal_local_geodesic_global ha y γ hlocal
  have hL : (pointSmoothConformalEDist a y x z).toReal = L := by
    have h := hglobal 0 1
    rw [hγ0, hγ1] at h
    simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero, abs_one, mul_one] using h
  exact ⟨γ, hγ0, hγ1, hγc, fun t ↦ (η t).2, fun s t ↦ by
    rw [hglobal s t, hL, mul_comm]⟩

/-- Every compact flat-clock subarc is ambient convex, including its two
artificial endpoints. The selected initial genuine corner is never used here. -/
theorem pointFlatBoundaryClockArc_geodesicallyConvex
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) (β : ℝ → ℂ)
    (hβ : IsClosedEmbedding β) (hfront : range β = frontier P)
    {s t : ℝ} (hst : s ≤ t)
    (hflat : ∀ u ∈ Icc s t, ∃ C : PointRetainedConeNeighborhood a y P (β u),
      C.flatPhysicalWidth = Real.pi) :
    PointGeodesicallyConvex a y (β '' Icc s t) := by
  have hclosed : IsClosed (β '' Icc s t) := (isCompact_Icc.image hβ.continuous).isClosed
  have hconn : IsPreconnected (β '' Icc s t) :=
    isPreconnected_Icc.image β hβ.continuous.continuousOn
  apply pointGeodesicallyConvex_of_localMinimizingChords ha y hclosed hconn
  rintro p ⟨u, hu, rfl⟩
  obtain ⟨C, hC⟩ := hflat u hu
  refine ⟨C.radius, C.radius_pos, ?_⟩
  rintro x ⟨v, hv, rfl⟩ z ⟨w, hw, rfl⟩ hvR hwR
  have hβfront (v : ℝ) : β v ∈ frontier P := hfront ▸ mem_range_self v
  obtain ⟨γ, h0, h1, hc, hγfront, hd⟩ := C.boundaryFlat_exists_chord
    ha y hP (hβfront u) hC (hβfront v) (hβfront w) hvR hwR
  have hβ' : @IsEmbedding ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace β := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact hβ.isEmbedding
  have hc' : @Continuous unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hγrange : range γ ⊆ range β := by
    rintro q ⟨r, rfl⟩
    rw [hfront]
    exact hγfront r
  have hsub := @ProperBoundaryEndClock.minimizing_chord_mem_clock_interval ℂ
    (pointSmoothConformalMetricSpace ha y) β hβ' v w γ hc' h0 h1 hγrange
    (fun r q ↦ by
      change (pointSmoothConformalEDist a y (γ r) (γ q)).toReal =
        |(r : ℝ) - (q : ℝ)| * (pointSmoothConformalEDist a y (β v) (β w)).toReal
      rw [abs_sub_comm]
      exact hd r q)
  refine ⟨γ, h0, h1, hc, ?_, hd⟩
  intro r
  obtain ⟨q, hq, he⟩ := hsub (mem_range_self r)
  refine ⟨q, ?_, he⟩
  exact (uIcc_subset_Icc hv hw) hq

end RepulsiveCoulomb
