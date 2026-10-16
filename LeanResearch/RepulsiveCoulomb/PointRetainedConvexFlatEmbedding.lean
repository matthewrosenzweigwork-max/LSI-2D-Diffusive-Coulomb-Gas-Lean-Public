import LeanResearch.RepulsiveCoulomb.PointConvexFlatClosedEmbedding
import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
import LeanResearch.RepulsiveCoulomb.MetricRegionPathTransport

/-! Adapter for an actual admissible residual region, and arbitrary curve
lengths. The admissibility theorem is the residualadmissible8 successor,
which must be admitted separately. It constructs intrinsic=ambient from
actual retained charts and minimizers. It is never a field assumed here.

This module still takes the actual local Euclidean map as input. It constructs
neither a positive-width strip nor a maximal sector, and asserts no coverage,
angular occupancy, first contact, or surgery/developing-map theorem.
-/
noncomputable section
open Set Topology
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The literal intrinsic local-isometry input is converted to the ambient
local-isometry input by the already constructed admissible-region geometry. -/
theorem pointRetained_localFlat_ambient
    {E : Type*} [PseudoMetricSpace E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    {f : E → P}
    (hf : ∀ p, ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∀ u ∈ V, ∀ v ∈ V,
      (pointRegionIntrinsicEDist ha y P (f u).1 (f v).1).toReal = dist u v) :
    PointLocallyDistancePreserving a y (fun x ↦ (f x).1) := by
  have heq := (pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y hP hconn hcharts).2
  intro p
  obtain ⟨V, hV, hp, hd⟩ := hf p
  refine ⟨V, hV, hp, ?_⟩
  intro u hu v hv
  rw [← heq _ (f u).2 _ (f v).2]
  exact hd u hu v hv

/-- All finite partition sums agree. This includes arbitrary curves, including
ones with infinitely many seam or chart crossings, and infinite variation.
The actual source/target map is only required to preserve all pairs. -/
theorem pointFlat_isometry_variation
    {E : Type*} [MetricSpace E] {A : Type*} [LinearOrder A]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (F : E → P)
    (hF : @Isometry E P (inferInstance : PseudoEMetricSpace E)
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace F)
    (γ : A → E) (s : Set A) :
    @eVariationOn A _ ℂ (pointSmoothConformalEMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℂ
        (pointSmoothConformalEMetricSpace ha y).toPseudoEMetricSpace)
      (fun t ↦ (F (γ t)).1) s = eVariationOn γ s := by
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  exact eVariationOn_map_eq_of_pairwise_edist F (P := univ)
    (fun x _ z _ ↦ hF x z) γ s (mapsTo_univ _ _)

/-- The manuscript's genuine metric-length convention, without a rectifiability
or finite-crossing assumption. In particular rectifiability is preserved. -/
theorem pointFlat_isometry_metricLength
    {E : Type*} [MetricSpace E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (F : E → P)
    (hF : @Isometry E P (inferInstance : PseudoEMetricSpace E)
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace F)
    (γ : ℝ → E) (s t : ℝ) :
    pointConformalMetricLength ha y (fun r ↦ (F (γ r)).1) s t =
      eVariationOn γ (Icc s t) :=
  pointFlat_isometry_variation ha y F hF γ (Icc s t)

/-- One usable closed-boundary endpoint for strips and sectors. The only
flat-map hypothesis is actual local intrinsic pair-distance preservation.
Its existence remains the task of the strip/sector continuation construction. -/
theorem pointRetained_convexFlat_closed_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set E} (hU : Convex ℝ U) {P : Set ℂ}
    (hP : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    (f : U → P)
    (hf : ∀ p, ∃ V : Set U, IsOpen V ∧ p ∈ V ∧ ∀ u ∈ V, ∀ v ∈ V,
      (pointRegionIntrinsicEDist ha y P (f u).1 (f v).1).toReal = dist u v) :
    ∃ F : closure U → P,
      (∀ x : U, F (flatClosureInclusion U x) = f x) ∧
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ x z, (pointRegionIntrinsicEDist ha y P (F x).1 (F z).1).toReal = dist x z) ∧
      IsClosedEmbedding (fun x ↦ (F x).1) ∧ IsProperMap (fun x ↦ (F x).1) ∧
      (∀ γ : ℝ → closure U, ∀ s t,
        pointConformalMetricLength ha y (fun r ↦ (F (γ r)).1) s t =
          eVariationOn γ (Icc s t)) ∧
      (∀ G : closure U → P, Continuous G →
        (∀ x : U, G (flatClosureInclusion U x) = f x) → G = F) := by
  have hamb := pointRetained_localFlat_ambient ha y hP hconn hcharts hf
  let F := pointFlatClosureMap ha y f
  have hiso := pointFlatClosureMap_isometry ha y hU hamb hP
  have hdist := pointFlatClosureMap_dist ha y hU hamb hP
  have heq := (pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y hP hconn hcharts).2
  obtain ⟨_, _, hclosed, hproper⟩ := pointFlatClosureMap_closed_proper ha y hU hamb hP
  refine ⟨F, pointFlatClosureMap_apply ha y hU hamb, hdist, ?_, hclosed, hproper, ?_, ?_⟩
  · intro x z
    rw [heq _ (F x).2 _ (F z).2]
    exact hdist x z
  · intro γ s t
    exact pointFlat_isometry_metricLength ha y F hiso γ s t
  · intro G hG hagree
    exact pointFlatClosureMap_unique ha y hG hagree

end RepulsiveCoulomb
