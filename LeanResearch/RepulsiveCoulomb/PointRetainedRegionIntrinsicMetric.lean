module

public import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

@[expose] public section

/-! A genuine intrinsic metric on the actual retained point-plane region.
The existing all-continuous-path infimum is identified with global clipped
representatives. Closedness, connectedness and actual retained interval charts
then give topology, properness, completeness and actual minimizing segments.
Admissibility and ambient convexity have not been used. -/
noncomputable section
open Set Topology
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointRegionIntrinsicEDist_eq_metricRegionPathEDist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ) (x z : ℂ) :
    pointRegionIntrinsicEDist ha y P x z =
      @metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) P x z := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    let f : ℝ → ℂ := @MetricRegionLengthPath.toFun ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z γ
    have hc' : @Continuous ℝ ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace f :=
      @MetricRegionLengthPath.continuous ℂ
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z γ
    have hc : Continuous f := by
      rwa [pointSmoothConformalMetricSpace_topology ha y] at hc'
    have h0 : f 0 = x := @MetricRegionLengthPath.source ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z γ
    have h1 : f 1 = z := @MetricRegionLengthPath.target ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z γ
    have hP : MapsTo f (Icc (0 : ℝ) 1) P := @MetricRegionLengthPath.mapsTo ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z γ
    let ξ : {g : ℝ → ℂ // g 0 = x ∧ g 1 = z ∧ ContinuousOn g (Icc (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) P} := ⟨f, h0, h1, hc.continuousOn, hP⟩
    have hle : pointRegionIntrinsicEDist ha y P x z ≤ pointConformalMetricLength ha y f 0 1 :=
      iInf_le _ ξ
    exact hle
  · apply le_iInf
    intro γ
    have hc : @ContinuousOn ℝ ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
        γ.1 (Icc (0 : ℝ) 1) := by
      rw [pointSmoothConformalMetricSpace_topology ha y]
      exact γ.2.2.2.1
    let η := @MetricRegionLengthPath.ofContinuousOn ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P x z
      γ.1 hc γ.2.1 γ.2.2.1 γ.2.2.2.2
    exact (@metricRegionPathEDist_le_length ℂ (pointSmoothConformalMetricSpace ha y) P x z η).trans_eq
      (@MetricRegionLengthPath.length_ofContinuousOn ℂ
        (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace P x z
        γ.1 hc γ.2.1 γ.2.2.1 γ.2.2.2.2)

/-- The metric is constructed from constrained curve lengths, rather than
inducing ambient distances on the subtype. -/
@[instance_reducible] def pointRetainedRegionIntrinsicMetricSpace {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ)
    (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) : MetricSpace P :=
  @metricRegionIntrinsicMetricSpace ℂ (pointSmoothConformalMetricSpace ha y) P
    (by rwa [pointSmoothConformalMetricSpace_topology ha y])
    (pointRetainedConeNeighborhoods_radialPaths ha y hcharts)

theorem pointRetainedRegionIntrinsicMetricSpace_edist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ)
    (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) (x z : P) :
    @edist P (pointRetainedRegionIntrinsicMetricSpace ha y P hconn hcharts).toEDist x z =
      pointRegionIntrinsicEDist ha y P x.1 z.1 := by
  rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
  rfl

theorem pointRetainedRegionIntrinsicMetricSpace_topology {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ)
    (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) :
    (pointRetainedRegionIntrinsicMetricSpace ha y P hconn hcharts).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P) := by
  have hc : @IsPreconnected ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have htop := @metricRegionIntrinsicMetricSpace_topology ℂ
    (pointSmoothConformalMetricSpace ha y) P hc (pointRetainedConeNeighborhoods_radialPaths ha y hcharts)
  apply htop.trans
  change TopologicalSpace.induced Subtype.val
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace =
    TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace ℂ)
  rw [pointSmoothConformalMetricSpace_topology ha y]

theorem pointRetainedRegionIntrinsicMetricSpace_proper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) :
    @ProperSpace P
      (pointRetainedRegionIntrinsicMetricSpace ha y P hconn hcharts).toPseudoMetricSpace := by
  exact @metricRegionIntrinsicMetricSpace_proper ℂ (pointSmoothConformalMetricSpace ha y)
    (pointSmoothConformalMetricSpace_proper ha y) P
    (by rwa [pointSmoothConformalMetricSpace_topology ha y])
    (by rwa [pointSmoothConformalMetricSpace_topology ha y])
    (pointRetainedConeNeighborhoods_radialPaths ha y hcharts)

theorem pointRetainedRegionIntrinsicMetricSpace_complete {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) :
    @CompleteSpace P
      (pointRetainedRegionIntrinsicMetricSpace ha y P hconn hcharts).toUniformSpace :=
  @complete_of_proper P
    (pointRetainedRegionIntrinsicMetricSpace ha y P hconn hcharts).toPseudoMetricSpace
    (pointRetainedRegionIntrinsicMetricSpace_proper ha y hclosed hconn hcharts)

theorem exists_pointRetainedRegion_intrinsic_geodesic {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p))
    (x z : P) :
    ∃ γ : unitInterval → P, γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧
      ∀ s t, (pointRegionIntrinsicEDist ha y P (γ s).1 (γ t).1).toReal =
        |t.1 - s.1| * (pointRegionIntrinsicEDist ha y P x.1 z.1).toReal := by
  obtain ⟨γ, h0, h1, hc, hd⟩ := @exists_metricRegionIntrinsic_geodesic ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y) P
    (by rwa [pointSmoothConformalMetricSpace_topology ha y])
    (by rwa [pointSmoothConformalMetricSpace_topology ha y])
    (pointRetainedConeNeighborhoods_radialPaths ha y hcharts) x z
  have hc' : Continuous γ := by
    change @Continuous unitInterval P _
      (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace γ at hc
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  refine ⟨γ, h0, h1, hc', ?_⟩
  intro s t
  simpa only [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y] using hd s t

end RepulsiveCoulomb
