import LeanResearch.RepulsiveCoulomb.ComplexLocalGeodesicStraightness
import LeanResearch.RepulsiveCoulomb.MetricMidpointGeodesic
import Mathlib.Topology.MetricSpace.Isometry

/-! Globalization of an actual locally distance-preserving map into the complex
plane. The segment hypothesis is the literal interface of the accepted
`exists_geodesic_of_exact_midpoints`: endpoint values, continuity, and all
pairwise minimizing distances. The pinned Mathlib contains no metric-geodesic
space typeclass, so no nonexistent interface or curvature surrogate is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

/-- Actual pairwise distance preservation on an open neighborhood of each point.
No injectivity, openness of the map, or global distance identity is included. -/
def LocallyDistancePreserving (F : X → ℂ) : Prop :=
  ∀ p, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
    ∀ u ∈ U, ∀ v ∈ U, dist (F u) (F v) = dist u v

/-- The image of an actual minimizing segment is locally a Euclidean
constant-speed minimizing curve. -/
theorem locallyDistancePreserving_comp_segment {F : X → ℂ}
    (hF : LocallyDistancePreserving F) {γ : Icc (0 : ℝ) 1 → X}
    (hγ : Continuous γ) {c : ℝ}
    (hd : ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * c) :
    LocallyConstantSpeedInterval c (F ∘ γ) := by
  intro t
  obtain ⟨U, hU, ht, hdist⟩ := hF (γ t)
  refine ⟨γ ⁻¹' U, hU.preimage hγ, ht, ?_⟩
  intro s hs u hu
  change dist (F (γ s)) (F (γ u)) = c * |u.1 - s.1|
  rw [hdist _ hs _ hu, hd, mul_comm]

/-- The image of each minimizing segment is globally affine with the original
constant-speed parameter. This is a consequence, not an assumed continuation
or global developing-map property. -/
theorem locallyDistancePreserving_segment_affine {F : X → ℂ}
    (hF : LocallyDistancePreserving F) {γ : Icc (0 : ℝ) 1 → X}
    (hγ : Continuous γ) {c : ℝ}
    (hd : ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * c)
    (t : Icc (0 : ℝ) 1) :
    F (γ t) = AffineMap.lineMap (F (γ ⟨0, by norm_num⟩))
      (F (γ ⟨1, by norm_num⟩)) t.1 :=
  complex_locallyConstantSpeedInterval_affine
    (locallyDistancePreserving_comp_segment hF hγ hd) t

/-- On a geodesic metric space, actual local pairwise distance preservation into
ℂ is globally an isometry. The only geometric hypothesis is existence of the
literal continuous minimizing segments between arbitrary endpoints. -/
theorem isometry_of_locallyDistancePreserving {F : X → ℂ}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hF : LocallyDistancePreserving F) : Isometry F := by
  apply Isometry.of_dist_eq
  intro x z
  obtain ⟨γ, h0, h1, hγ, hd⟩ := hsegment x z
  have hdist := complex_locallyConstantSpeedInterval_endpoint_distance
    (locallyDistancePreserving_comp_segment hF hγ hd)
  simpa only [Function.comp_apply, h0, h1] using hdist

/-- Complete metric spaces with actual exact midpoints supply the segment
hypothesis by the campaign's accepted dyadic-limit construction. -/
theorem isometry_of_locallyDistancePreserving_of_exact_midpoints
    [CompleteSpace X] {F : X → ℂ}
    (hmid : ∀ x z : X, ∃ p, dist x p = dist x z / 2 ∧ dist p z = dist x z / 2)
    (hF : LocallyDistancePreserving F) : Isometry F :=
  isometry_of_locallyDistancePreserving (exists_geodesic_of_exact_midpoints hmid) hF

end RepulsiveCoulomb
