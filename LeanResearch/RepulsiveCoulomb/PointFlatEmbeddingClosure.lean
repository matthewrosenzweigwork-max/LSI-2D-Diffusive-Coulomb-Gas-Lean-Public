module

public import LeanResearch.RepulsiveCoulomb.PointFlatEmbeddingOpenImage
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Closed ranges, density of the literal source
interior image, and exclusion of another open sector from the closed image.
These facts are derived for actual maps, not stored as seam certificates. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointFlatEmbedding_isClosedEmbedding
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsClosed K) (f : K → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    IsClosedEmbedding f := by
  letI : CompleteSpace K := hK.isComplete.completeSpace_coe
  have hi : @Isometry K ℂ (inferInstance : PseudoEMetricSpace K)
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace f := by
    apply @Isometry.of_dist_eq K ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    exact hd
  have hc : @IsClosedEmbedding K ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace f :=
    @Isometry.isClosedEmbedding K ℂ (inferInstance : EMetricSpace K)
      (inferInstance : CompleteSpace K) (pointSmoothConformalMetricSpace ha y).toEMetricSpace f hi
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

/-- A nondegenerate closed convex source has dense relative interior. Under
the actual closed embedding, its image closure is exactly the full range. -/
theorem pointFlatEmbedding_closure_openImage
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsClosed K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) (f : K → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    closure (f '' {x : K | x.1 ∈ interior K}) = range f := by
  have hclosure : closure (interior K) = K :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans hK.closure_eq
  have hrel : closure {x : K | x.1 ∈ interior K} = univ := by
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change Subtype.val ⁻¹' closure (Subtype.val '' (Subtype.val ⁻¹' interior K)) = univ
    rw [Subtype.image_preimage_val, inter_eq_right.mpr interior_subset, hclosure]
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  rw [(pointFlatEmbedding_isClosedEmbedding ha y hK f hd).closure_image_eq, hrel, image_univ]

/-- No boundary of the first sector can lie inside the other open sector.
Only the already proved closure and ambient openness are used. -/
theorem pointFlatEmbedding_range_disjoint_openImage
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K T : Set ℂ} (hK : IsClosed K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) (f : K → ℂ) (g : T → ℂ)
    (hf : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (hg : ∀ x z, (pointSmoothConformalEDist a y (g x) (g z)).toReal = dist x z)
    (hregular : ∀ x : T, x.1 ∈ interior T → coalescedPointExponent a y (g x) = 0)
    (hdis : Disjoint (f '' {x : K | x.1 ∈ interior K})
      (g '' {x : T | x.1 ∈ interior T})) :
    Disjoint (range f) (g '' {x : T | x.1 ∈ interior T}) := by
  rw [← pointFlatEmbedding_closure_openImage ha y hK hconv hne f hf]
  exact hdis.closure_left (pointFlatEmbedding_isOpen_openImage ha y g hg hregular)

end RepulsiveCoulomb
