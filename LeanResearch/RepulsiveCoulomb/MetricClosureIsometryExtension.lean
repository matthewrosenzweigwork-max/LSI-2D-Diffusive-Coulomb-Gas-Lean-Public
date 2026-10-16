import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Maps.Proper.Basic

/-! Extend an already proved isometry from a literal subset to its closure.

This is Mathlib's dense uniform-extension construction: completeness is used
by `uniformContinuous_uniformly_extend` to take actual Cauchy-filter limits.
All-pairs distance equality passes to those limits through a closed two-point
relation. This module adds the literal-closure interface; it does not replace
or assume a local-to-global geometric theorem.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb
variable {E Y : Type*} [MetricSpace E] [MetricSpace Y]

/-- The canonical inclusion of a subset into its literal ambient closure. -/
def flatClosureInclusion (U : Set E) : U → closure U := inclusion subset_closure

theorem flatClosureInclusion_isometry (U : Set E) : Isometry (flatClosureInclusion U) :=
  fun _ _ ↦ rfl

theorem flatClosureInclusion_denseRange (U : Set E) : DenseRange (flatClosureInclusion U) := by
  exact (denseRange_inclusion_iff (subset_closure : U ⊆ closure U)).mpr subset_rfl

/-- The actual Cauchy extension along the dense inclusion. Its useful
properties below require the original map to be an isometry and Y complete. -/
def flatIsometryClosureExtension {U : Set E} (f : U → Y) : closure U → Y :=
  ((flatClosureInclusion_isometry U).isUniformInducing.isDenseInducing
    (flatClosureInclusion_denseRange U)).extend f

@[simp] theorem flatIsometryClosureExtension_apply {U : Set E} {f : U → Y}
    (hf : Isometry f) (x : U) :
    flatIsometryClosureExtension f (flatClosureInclusion U x) = f x := by
  exact IsDenseInducing.extend_eq _ hf.continuous x

theorem continuous_flatIsometryClosureExtension [CompleteSpace Y]
    {U : Set E} {f : U → Y} (hf : Isometry f) :
    Continuous (flatIsometryClosureExtension f) := by
  exact (uniformContinuous_uniformly_extend (flatClosureInclusion_isometry U).isUniformInducing
    (flatClosureInclusion_denseRange U) hf.uniformContinuous).continuous

/-- All-pairs equality holds even when both points are newly added boundary
points. It is not merely radial or basepoint distance preservation. -/
theorem flatIsometryClosureExtension_isometry [CompleteSpace Y]
    {U : Set E} {f : U → Y} (hf : Isometry f) :
    Isometry (flatIsometryClosureExtension f) := by
  apply Isometry.of_dist_eq
  have hc := continuous_flatIsometryClosureExtension hf
  refine isClosed_property2
    (p := fun x z : closure U ↦
      dist (flatIsometryClosureExtension f x) (flatIsometryClosureExtension f z) = dist x z)
    (flatClosureInclusion_denseRange U) ?_ ?_
  · exact isClosed_eq ((hc.comp continuous_fst).dist (hc.comp continuous_snd))
      (continuous_fst.dist continuous_snd)
  · intro x z
    rw [flatIsometryClosureExtension_apply hf, flatIsometryClosureExtension_apply hf,
      (flatClosureInclusion_isometry U).dist_eq]
    exact hf.dist_eq x z

/-- Uniqueness holds amongst all continuous extensions, not only isometries. -/
theorem flatIsometryClosureExtension_unique {U : Set E} (f : U → Y)
    {g : closure U → Y} (hg : Continuous g)
    (hagree : ∀ x : U, g (flatClosureInclusion U x) = f x) :
    g = flatIsometryClosureExtension f := by
  exact (((flatClosureInclusion_isometry U).isUniformInducing.isDenseInducing
    (flatClosureInclusion_denseRange U)).extend_unique hagree hg).symm

/-- A closed Euclidean domain is complete. A complete-domain isometry has
closed image, so it is a proper topological map into any metric target. -/
theorem flatIsometryClosureExtension_closed_proper [CompleteSpace E] [CompleteSpace Y]
    {U : Set E} {f : U → Y} (hf : Isometry f) :
    IsClosedEmbedding (flatIsometryClosureExtension f) ∧
      IsProperMap (flatIsometryClosureExtension f) := by
  letI : CompleteSpace (closure U) := isClosed_closure.isComplete.completeSpace_coe
  have hclosed := (flatIsometryClosureExtension_isometry hf).isClosedEmbedding
  exact ⟨hclosed, hclosed.isProperMap⟩

end RepulsiveCoulomb
