module

public import LeanResearch.RepulsiveCoulomb.MetricRayHalfDiskPatchCompatibility
public import Mathlib.Data.Set.UnionLift

@[expose] public section

/-! NEW source-only implementation. Glue actual aligned metric halfdisk
patches along a minimizing ray. Compatibility comes from the genuine-chart
construction. The conclusion is local distance preservation; no arbitrary
metric-target local-to-global assertion is made. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The actual union of the constructed upper halfdisk sources. -/
def flatRayHalfDiskPatchedSet {ι : Type*} (r : ι → NNReal) (ε : ι → ℝ) : Set ℂ :=
  ⋃ i, flatRayHalfDisk (r i) (ε i)

/-- Genuine charts construct a compatible union map, its bottom matching,
its relative-local distance identities, and full charts above the bottom. -/
theorem exists_metricRay_halfDisk_patched_union {Y ι : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) (r : ι → NNReal) (hr : ∀ i, 0 < r i)
    (C : ∀ i, MetricFlatHalfDiskChart Y (ρ (r i))) :
    ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧
      ∃ G : flatRayHalfDiskPatchedSet r ε → Y,
        (∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatRayHalfDiskPatchedSet r ε,
          G ⟨(t : ℂ), ht⟩ = ρ t) ∧
        (∀ p, ∃ V : Set (flatRayHalfDiskPatchedSet r ε), IsOpen V ∧ p ∈ V ∧
          ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z) ∧
        ∀ z, 0 < z.1.im → Nonempty (MetricFlatDiskChart Y (G z)) := by
  obtain ⟨ε, hε, F, hF, hFb, hcompat, hreg⟩ :=
    exists_compatible_metricRay_halfDisk_patches ρ hρ r hr C
  let D : ι → Set ℂ := fun i ↦ flatRayHalfDisk (r i) (ε i)
  have hsub : flatRayHalfDiskPatchedSet r ε ⊆ ⋃ i, D i := fun _ hz ↦ hz
  let G : flatRayHalfDiskPatchedSet r ε → Y := iUnionLift D F hcompat _ hsub
  have hGpatch (p : flatRayHalfDiskPatchedSet r ε) (i : ι) (hi : p.1 ∈ D i) :
      G p = F i ⟨p.1, hi⟩ :=
    iUnionLift_of_mem (S := D) (f := F) (hf := hcompat) (hT := hsub) p hi
  have hnonneg (p : flatRayHalfDiskPatchedSet r ε) : 0 ≤ p.1.im := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub p.2)
    exact hi.2
  refine ⟨ε, hε, G, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub ht)
    exact (hGpatch ⟨(t : ℂ), ht⟩ i hi).trans (hFb i t hi)
  · intro p
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub p.2)
    let V : Set (flatRayHalfDiskPatchedSet r ε) :=
      Subtype.val ⁻¹' ball (r i : ℂ) (ε i)
    refine ⟨V, isOpen_ball.preimage continuous_subtype_val, hi.1, ?_⟩
    intro x hx z hz
    have hxi : x.1 ∈ D i := ⟨hx, hnonneg x⟩
    have hzi : z.1 ∈ D i := ⟨hz, hnonneg z⟩
    rw [hGpatch x i hxi, hGpatch z i hzi]
    exact (hF i).dist_eq _ _
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub z.2)
    rw [hGpatch z i hi]
    exact hreg i ⟨z.1, hi⟩ hz

end RepulsiveCoulomb
