import LeanResearch.RepulsiveCoulomb.PointActualGeodesicContinuation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Convex Euclidean domains mapping into the actual conformal plane.

The map and its literal local distance identities are inputs. Straight segments
are constructed in the source, including both endpoint witnesses. Their images
are actual ambient local geodesics, so the accepted ambient local-to-global
result proves all-pairs distance preservation. No injectivity, developing map,
metric globalization certificate, or strip/sector existence is assumed.

The source can be any real normed vector space. Openness is unnecessary once
local distance preservation is stated in the relative source topology; in the
applications the source is an open convex strip or a sector of angle at most pi.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Literal local pair-distance preservation into the conformal plane. This is
not the accepted `LocallyDistancePreserving`, whose target metric is Euclidean. -/
def PointLocallyDistancePreserving {X : Type*} [PseudoMetricSpace X]
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (f : X → ℂ) : Prop :=
  ∀ p, ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ ∀ u ∈ V, ∀ v ∈ V,
    (pointSmoothConformalEDist a y (f u) (f v)).toReal = dist u v

section SourceSegment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U)

/-- The actual straight segment, with values in the literal convex source set. -/
def convexDomainSegment (x z : U) : Icc (0 : ℝ) 1 → U :=
  fun t ↦ ⟨AffineMap.lineMap x.1 z.1 t.1, hU.lineMap_mem x.2 z.2 t.2⟩

@[simp] theorem convexDomainSegment_zero (x z : U) :
    convexDomainSegment hU x z ⟨0, by norm_num⟩ = x := by
  apply Subtype.ext
  simp [convexDomainSegment]

@[simp] theorem convexDomainSegment_one (x z : U) :
    convexDomainSegment hU x z ⟨1, by norm_num⟩ = z := by
  apply Subtype.ext
  simp [convexDomainSegment]

theorem continuous_convexDomainSegment (x z : U) :
    Continuous (convexDomainSegment hU x z) := by
  unfold convexDomainSegment
  apply Continuous.subtype_mk
  exact (lipschitzWith_lineMap x.1 z.1).continuous.comp continuous_subtype_val

/-- All source parameters, including reversed and equal parameters. -/
theorem convexDomainSegment_dist (x z : U) (s t : Icc (0 : ℝ) 1) :
    dist (convexDomainSegment hU x z s) (convexDomainSegment hU x z t) =
      dist x z * |t.1 - s.1| := by
  change dist (AffineMap.lineMap x.1 z.1 s.1) (AffineMap.lineMap x.1 z.1 t.1) =
    dist x.1 z.1 * |t.1 - s.1|
  rw [dist_lineMap_lineMap, Real.dist_eq, abs_sub_comm, mul_comm]

end SourceSegment

/-- Pull back the actual local-isometry neighborhoods along an actual
continuous constant-speed source segment. No global target identity is input. -/
theorem pointLocallyDistancePreserving_comp_segment
    {X : Type*} [PseudoMetricSpace X] {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {f : X → ℂ} (hf : PointLocallyDistancePreserving a y f)
    {γ : Icc (0 : ℝ) 1 → X} (hγ : Continuous γ) {c : ℝ}
    (hd : ∀ s t, dist (γ s) (γ t) = c * |t.1 - s.1|) :
    ∀ t, ∃ V : Set (Icc (0 : ℝ) 1), IsOpen V ∧ t ∈ V ∧
      ∀ s ∈ V, ∀ u ∈ V,
        (pointSmoothConformalEDist a y (f (γ s)) (f (γ u))).toReal = c * |u.1 - s.1| := by
  intro t
  obtain ⟨V, hV, ht, hdist⟩ := hf (γ t)
  refine ⟨γ ⁻¹' V, hV.preimage hγ, ht, ?_⟩
  intro s hs u hu
  exact (hdist _ hs _ hu).trans (hd s u)

section Globalize
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set E} (hU : Convex ℝ U) {f : U → ℂ}
    (hf : PointLocallyDistancePreserving a y f)

include ha hU hf

/-- A mapped straight segment is globally minimizing at its original speed.
This invokes the accepted actual ambient no-shortcut theorem. -/
theorem pointConvexFlat_segment_distance (x z : U) (s t : Icc (0 : ℝ) 1) :
    (pointSmoothConformalEDist a y
      (f (convexDomainSegment hU x z s)) (f (convexDomainSegment hU x z t))).toReal =
        dist x z * |t.1 - s.1| := by
  exact pointConformal_local_geodesic_global ha y (f ∘ convexDomainSegment hU x z)
    (pointLocallyDistancePreserving_comp_segment hf
      (continuous_convexDomainSegment hU x z) (convexDomainSegment_dist hU x z)) s t

/-- The endpoint witnesses of the constructed straight segment give the
all-pairs identity. In particular injectivity is a conclusion. -/
theorem pointConvexFlat_dist (x z : U) :
    (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z := by
  have h := pointConvexFlat_segment_distance ha y hU hf x z
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  simpa only [convexDomainSegment_zero, convexDomainSegment_one,
    sub_zero, abs_one, mul_one] using h

theorem pointConvexFlat_isometry :
    @Isometry U ℂ (inferInstance : PseudoEMetricSpace U)
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace f := by
  apply @Isometry.of_dist_eq U ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace f
  exact pointConvexFlat_dist ha y hU hf

/-- Actual endpoint, continuity and full parameter-pair witnesses for the
mapped segment. Its range remains in the range of the given map. -/
theorem pointConvexFlat_image_segment (x z : U) :
    ∃ γ : Icc (0 : ℝ) 1 → ℂ,
      γ ⟨0, by norm_num⟩ = f x ∧ γ ⟨1, by norm_num⟩ = f z ∧ Continuous γ ∧
      (∀ t, γ t ∈ range f) ∧ ∀ s t,
        (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist x z * |t.1 - s.1| := by
  let γ := f ∘ convexDomainSegment hU x z
  have hc : @Continuous U ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace f := by
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    exact (pointConvexFlat_isometry ha y hU hf).continuous
  rw [pointSmoothConformalMetricSpace_topology ha y] at hc
  refine ⟨γ, ?_, ?_, hc.comp (continuous_convexDomainSegment hU x z), ?_, ?_⟩
  · exact congrArg f (convexDomainSegment_zero hU x z)
  · exact congrArg f (convexDomainSegment_one hU x z)
  · intro t
    exact ⟨convexDomainSegment hU x z t, rfl⟩
  · exact pointConvexFlat_segment_distance ha y hU hf x z

end Globalize
end RepulsiveCoulomb
