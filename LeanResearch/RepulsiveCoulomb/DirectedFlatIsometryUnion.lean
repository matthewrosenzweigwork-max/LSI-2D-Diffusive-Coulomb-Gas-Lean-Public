import LeanResearch.RepulsiveCoulomb.MetricClosureIsometryExtension
import Mathlib.Data.Set.UnionLift

/-! Directed union and actual Cauchy completion for compatible isometries.
The compatibility hypothesis is stated openly: this module does not construct
chart continuation, prove compatibility, or assert a maximal family's existence.
It discharges the limiting-map step once the genuine chart construction has
produced a compatible directed family. No attainment hypothesis is used. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb
variable {E Y ι : Type*} [MetricSpace E] [MetricSpace Y]

/-- Glue the literal maps using their verified overlap equalities. -/
def directedFlatUnion (U : ι → Set E) (f : ∀ i, U i → Y)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    (⋃ i, U i) → Y := iUnionLift U f hcompat (⋃ i, U i) subset_rfl

@[simp] theorem directedFlatUnion_apply (U : ι → Set E) (f : ∀ i, U i → Y)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (i : ι) (x : U i) :
    directedFlatUnion U f hcompat ⟨x.1, mem_iUnion.mpr ⟨i, x.2⟩⟩ = f i x := by
  exact iUnionLift_mk x _

theorem directedFlatUnion_of_mem (U : ι → Set E) (f : ∀ i, U i → Y)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (x : ⋃ i, U i) (i : ι) (hi : x.1 ∈ U i) :
    directedFlatUnion U f hcompat x = f i ⟨x.1, hi⟩ := by
  exact iUnionLift_of_mem x hi

/-- Any two source points lie in one stage. Its already proved isometry gives
the union's all-pairs distance identity, including arbitrarily distant points. -/
theorem directedFlatUnion_isometry (U : ι → Set E) (f : ∀ i, U i → Y)
    (hdir : Directed (· ⊆ ·) U)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hf : ∀ i, Isometry (f i)) : Isometry (directedFlatUnion U f hcompat) := by
  apply Isometry.of_dist_eq
  intro x z
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.2
  obtain ⟨j, hj⟩ := mem_iUnion.mp z.2
  obtain ⟨k, hik, hjk⟩ := hdir i j
  rw [directedFlatUnion_of_mem U f hcompat x k (hik hi),
    directedFlatUnion_of_mem U f hcompat z k (hjk hj)]
  exact (hf k).dist_eq _ _

/-- The width-limit or unbounded-length map is constructed using the complete
target. No maximal-family attainment or limiting map is supplied as a field. -/
def directedFlatClosure (U : ι → Set E) (f : ∀ i, U i → Y)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    closure (⋃ i, U i) → Y := flatIsometryClosureExtension (directedFlatUnion U f hcompat)

@[simp] theorem directedFlatClosure_apply (U : ι → Set E) (f : ∀ i, U i → Y)
    (hdir : Directed (· ⊆ ·) U)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hf : ∀ i, Isometry (f i)) (i : ι) (x : U i) :
    directedFlatClosure U f hcompat
      ⟨x.1, subset_closure (mem_iUnion.mpr ⟨i, x.2⟩)⟩ = f i x := by
  have h := flatIsometryClosureExtension_apply (directedFlatUnion_isometry U f hdir hcompat hf)
    (⟨x.1, mem_iUnion.mpr ⟨i, x.2⟩⟩ : ⋃ i, U i)
  exact h.trans (directedFlatUnion_apply U f hcompat i x)

theorem directedFlatClosure_isometry [CompleteSpace Y]
    (U : ι → Set E) (f : ∀ i, U i → Y) (hdir : Directed (· ⊆ ·) U)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hf : ∀ i, Isometry (f i)) : Isometry (directedFlatClosure U f hcompat) :=
  flatIsometryClosureExtension_isometry (directedFlatUnion_isometry U f hdir hcompat hf)

/-- An already anchored bottom point retains its exact distance to every new
boundary-limit point. This is the precise input to the uniform-clearance lemma. -/
theorem directedFlatClosure_dist_to_stage [CompleteSpace Y]
    (U : ι → Set E) (f : ∀ i, U i → Y) (hdir : Directed (· ⊆ ·) U)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hf : ∀ i, Isometry (f i)) (i : ι) (x : U i) (z : closure (⋃ i, U i)) :
    dist (directedFlatClosure U f hcompat z) (f i x) = dist z.1 x.1 := by
  rw [← directedFlatClosure_apply U f hdir hcompat hf i x]
  exact (directedFlatClosure_isometry U f hdir hcompat hf).dist_eq _ _

theorem directedFlatClosure_closed_proper [CompleteSpace E] [CompleteSpace Y]
    (U : ι → Set E) (f : ∀ i, U i → Y) (hdir : Directed (· ⊆ ·) U)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hf : ∀ i, Isometry (f i)) :
    IsClosedEmbedding (directedFlatClosure U f hcompat) ∧
      IsProperMap (directedFlatClosure U f hcompat) :=
  flatIsometryClosureExtension_closed_proper (directedFlatUnion_isometry U f hdir hcompat hf)

/-- Every continuous extension agreeing with all finite stages is the same
actual Cauchy extension, also at the completed top and side boundaries. -/
theorem directedFlatClosure_unique (U : ι → Set E) (f : ∀ i, U i → Y)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    {g : closure (⋃ i, U i) → Y} (hg : Continuous g)
    (hagree : ∀ i (x : U i), g ⟨x.1, subset_closure (mem_iUnion.mpr ⟨i, x.2⟩)⟩ = f i x) :
    g = directedFlatClosure U f hcompat := by
  apply flatIsometryClosureExtension_unique _ hg
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.2
  exact (hagree i ⟨x.1, hi⟩).trans (directedFlatUnion_of_mem U f hcompat x i hi).symm

end RepulsiveCoulomb
