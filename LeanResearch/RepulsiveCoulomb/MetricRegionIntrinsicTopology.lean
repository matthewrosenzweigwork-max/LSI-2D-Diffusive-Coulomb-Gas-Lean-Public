import LeanResearch.RepulsiveCoulomb.MetricRegionPathDistance
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Topology and properness of the genuine constrained intrinsic metric.
Only radial competitors from each local chart center are used. No ambient
convexity or equality of arbitrary pair distances is assumed. -/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

theorem dist_le_metricRegionIntrinsicDist {P : Set X}
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) (x z : P) :
    dist x.1 z.1 ≤ @dist P (metricRegionIntrinsicMetricSpace P hconn hlocal).toDist x z := by
  rw [dist_edist]
  exact ENNReal.toReal_mono
    (metricRegionPathEDist_lt_top_of_connected hconn hlocal x.2 z.2).ne
    (edist_le_metricRegionPathEDist P x.1 z.1)

theorem metricRegionIntrinsicMetricSpace_topology {P : Set X}
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) :
    (metricRegionIntrinsicMetricSpace P hconn hlocal).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P) := by
  let dP := metricRegionIntrinsicMetricSpace P hconn hlocal
  have hforward : @Continuous P P dP.toUniformSpace.toTopologicalSpace inferInstance id := by
    have hLip : @LipschitzWith P P dP.toPseudoEMetricSpace inferInstance 1 id := by
      intro x z
      change edist x.1 z.1 ≤ (1 : ℝ≥0∞) * metricRegionPathEDist P x.1 z.1
      simpa only [one_mul] using edist_le_metricRegionPathEDist P x.1 z.1
    exact @LipschitzWith.continuous P P dP.toPseudoEMetricSpace inferInstance 1 id hLip
  have hbackward : @Continuous P P inferInstance dP.toUniformSpace.toTopologicalSpace id := by
    apply (@Metric.continuous_iff P P inferInstance dP.toPseudoMetricSpace id).mpr
    intro x ε hε
    obtain ⟨r, hr, heq⟩ := metricRegionPathEDist_center_eq hlocal x.2
    refine ⟨min r ε, lt_min hr hε, ?_⟩
    intro z hz
    have hz' : dist z.1 x.1 < r := hz.trans_le (min_le_left _ _)
    change (metricRegionPathEDist P z.1 x.1).toReal < ε
    rw [metricRegionPathEDist_comm P z.1 x.1, heq z.1 z.2 hz', ← dist_edist, dist_comm]
    exact hz.trans_le (min_le_right _ _)
  exact le_antisymm (continuous_id_iff_le.mp hforward) (continuous_id_iff_le.mp hbackward)

theorem metricRegionIntrinsicMetricSpace_proper [ProperSpace X] {P : Set X}
    (hclosed : IsClosed P) (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) :
    @ProperSpace P (metricRegionIntrinsicMetricSpace P hconn hlocal).toPseudoMetricSpace := by
  let dP := metricRegionIntrinsicMetricSpace P hconn hlocal
  letI : ProperSpace P := ProperSpace.of_isClosed hclosed
  refine @ProperSpace.mk P dP.toPseudoMetricSpace ?_
  intro x r
  let S := {z : P | (metricRegionPathEDist P z.1 x.1).toReal ≤ r}
  have hS : IsClosed S := by
    have h := @isClosed_closedBall P dP.toPseudoMetricSpace x r
    change @IsClosed P
      (metricRegionIntrinsicMetricSpace P hconn hlocal).toUniformSpace.toTopologicalSpace S at h
    rwa [metricRegionIntrinsicMetricSpace_topology hconn hlocal] at h
  change @IsCompact P
    (metricRegionIntrinsicMetricSpace P hconn hlocal).toUniformSpace.toTopologicalSpace S
  rw [metricRegionIntrinsicMetricSpace_topology hconn hlocal]
  apply (isCompact_closedBall x r).of_isClosed_subset hS
  intro z hz
  exact (dist_le_metricRegionIntrinsicDist hconn hlocal z x).trans hz

theorem metricRegionIntrinsicMetricSpace_complete [ProperSpace X] {P : Set X}
    (hclosed : IsClosed P) (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) :
    @CompleteSpace P (metricRegionIntrinsicMetricSpace P hconn hlocal).toUniformSpace :=
  @complete_of_proper P (metricRegionIntrinsicMetricSpace P hconn hlocal).toPseudoMetricSpace
    (metricRegionIntrinsicMetricSpace_proper hclosed hconn hlocal)

end RepulsiveCoulomb
