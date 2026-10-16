import LeanResearch.RepulsiveCoulomb.PointConvexLocalFlatEmbedding
import LeanResearch.RepulsiveCoulomb.MetricClosureIsometryExtension
import LeanResearch.RepulsiveCoulomb.PointClosedRegionIntrinsicMetric

/-! The literal closed-boundary extension into a closed region P.

The region metric used in this module is explicitly the ambient restriction.
No equality with the constrained intrinsic infimum is used or asserted here.
The next residual-region adapter obtains that equality from actual retained
charts and admissibility, rather than hiding it in this metric definition.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Actual local pair distances give an isometry into the ambient-restriction
metric on P. The map's values are required to lie in P. -/
theorem pointConvexFlat_subtype_isometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set E} (hU : Convex ℝ U) {P : Set ℂ} {f : U → P}
    (hf : PointLocallyDistancePreserving a y (fun x ↦ (f x).1)) :
    @Isometry U P (inferInstance : PseudoEMetricSpace U)
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f := by
  apply @Isometry.of_dist_eq U P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace f
  exact pointConvexFlat_dist ha y hU hf

/-- Canonical actual extension; no chart or polar-direction choices occur. -/
def pointFlatClosureMap {E : Type*} [MetricSpace E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set E} {P : Set ℂ} (f : U → P) : closure U → P :=
  @flatIsometryClosureExtension E P _ (pointRegionMetricSpace ha y P) U f

section ClosedExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set E} (hU : Convex ℝ U) {P : Set ℂ} {f : U → P}
    (hf : PointLocallyDistancePreserving a y (fun x ↦ (f x).1))

include hU hf

@[simp] theorem pointFlatClosureMap_apply (x : U) :
    pointFlatClosureMap ha y f (flatClosureInclusion U x) = f x := by
  exact @flatIsometryClosureExtension_apply E P _ (pointRegionMetricSpace ha y P) U f
    (pointConvexFlat_subtype_isometry ha y hU hf) x

theorem pointFlatClosureMap_isometry (hP : IsClosed P) :
    @Isometry (closure U) P (inferInstance : PseudoEMetricSpace (closure U))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace (pointFlatClosureMap ha y f) := by
  exact @flatIsometryClosureExtension_isometry E P _ (pointRegionMetricSpace ha y P)
    (pointRegionMetricSpace_complete ha y hP) U f (pointConvexFlat_subtype_isometry ha y hU hf)

/-- The formula includes two boundary points and all cross-boundary pairs. -/
theorem pointFlatClosureMap_dist (hP : IsClosed P) (x z : closure U) :
    (pointSmoothConformalEDist a y (pointFlatClosureMap ha y f x).1
      (pointFlatClosureMap ha y f z).1).toReal = dist x z := by
  exact @Isometry.dist_eq (closure U) P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
    (pointFlatClosureMap ha y f) (pointFlatClosureMap_isometry ha y hU hf hP) x z

/-- Continuity is in the original Euclidean subspace topologies. -/
theorem continuous_pointFlatClosureMap (hP : IsClosed P) :
    Continuous (pointFlatClosureMap ha y f) := by
  have hc : @Continuous (closure U) P _
      (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      (pointFlatClosureMap ha y f) := by
    exact @Isometry.continuous (closure U) P _
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
      (pointFlatClosureMap ha y f) (pointFlatClosureMap_isometry ha y hU hf hP)
  rwa [pointRegionMetricSpace_topology ha y P] at hc

omit hU hf

/-- Every continuous closed-boundary extension agrees, including at every
source edge and vertex. No finite boundary subdivision is required. -/
theorem pointFlatClosureMap_unique {g : closure U → P} (hg : Continuous g)
    (hagree : ∀ x : U, g (flatClosureInclusion U x) = f x) :
    g = pointFlatClosureMap ha y f := by
  have hg' : @Continuous (closure U) P _
      (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace g := by
    rwa [pointRegionMetricSpace_topology ha y P]
  exact @flatIsometryClosureExtension_unique E P _ (pointRegionMetricSpace ha y P) U f g hg' hagree

include hU hf

/-- Properness and closed embedding hold in the actual ambient topological
plane as well as in P. For Euclidean source domains, completeness is automatic. -/
theorem pointFlatClosureMap_closed_proper [CompleteSpace E] (hP : IsClosed P) :
    IsClosedEmbedding (pointFlatClosureMap ha y f) ∧
      IsProperMap (pointFlatClosureMap ha y f) ∧
      IsClosedEmbedding (fun x ↦ (pointFlatClosureMap ha y f x).1) ∧
      IsProperMap (fun x ↦ (pointFlatClosureMap ha y f x).1) := by
  letI : CompleteSpace (closure U) := isClosed_closure.isComplete.completeSpace_coe
  have hc : @IsClosedEmbedding (closure U) P _
      (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      (pointFlatClosureMap ha y f) := by
    exact @Isometry.isClosedEmbedding (closure U) P
      (inferInstance : EMetricSpace (closure U))
      (inferInstance : CompleteSpace (closure U)) (pointRegionMetricSpace ha y P).toEMetricSpace
      (pointFlatClosureMap ha y f) (pointFlatClosureMap_isometry ha y hU hf hP)
  rw [pointRegionMetricSpace_topology ha y P] at hc
  have hamb := hP.isClosedEmbedding_subtypeVal.comp hc
  exact ⟨hc, hc.isProperMap, hamb, hamb.isProperMap⟩

end ClosedExtension
end RepulsiveCoulomb
