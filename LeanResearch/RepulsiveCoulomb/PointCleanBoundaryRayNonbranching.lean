module

public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskRayNonbranching
public import LeanResearch.RepulsiveCoulomb.PointCleanRayRetainedHalfDisks

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. Actual clean old-boundary rays are nonbranching
INSIDE the genuine retained region. Ambient cone atoms are allowed: signed
boundary coefficient zero gives physical retained angle pi and the needed
whole relative metric halfdisk. No ambient flatness assumption is made.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem pointCleanBoundaryRay_eq_of_positive_prefix
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (hν : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    (f g : NNReal → P)
    (hf : @Isometry NNReal P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hg : @Isometry NNReal P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace g)
    (hfront : ∀ t, (g t).1 ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(g 0).1})
      (range (fun t ↦ (g t).1)))
    {ε : ℝ} (hε : 0 < ε) (hseed : ∀ t : NNReal, t.1 ≤ ε → f t = g t) :
    f = g := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  apply metricHalfDisk_ray_prefix_continuation f g hf hg
    (fun t ht ↦ pointCleanRay_exists_actual_retained_halfDisk
      ha y hν g hg hfront hclean t ht) hε hseed

end RepulsiveCoulomb
