module

public import LeanResearch.RepulsiveCoulomb.FiniteTranspositionGap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

@[expose] public section

/-! Restrict a genuine finite-group representation to the finite-dimensional orbit span. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteOrbitSpan (U : G →* (E →L[ℝ] E)) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun g => U g x))

instance finiteOrbitSpan_finiteDimensional (U : G →* (E →L[ℝ] E)) (x : E) :
    FiniteDimensional ℝ (finiteOrbitSpan U x) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem finiteOrbitSpan_self (U : G →* (E →L[ℝ] E)) (x : E) : x ∈ finiteOrbitSpan U x := by
  have h : U 1 x ∈ finiteOrbitSpan U x := Submodule.subset_span (Set.mem_range_self 1)
  simpa using h

theorem finiteOrbitSpan_invariant (U : G →* (E →L[ℝ] E)) (x : E) (g : G) :
    ∀ y ∈ finiteOrbitSpan U x, U g y ∈ finiteOrbitSpan U x := by
  apply Submodule.mapsTo_span (f := (U g).toLinearMap)
  intro y hy
  obtain ⟨h,rfl⟩ := hy
  refine ⟨g * h, ?_⟩
  change U (g * h) x = U g (U h x)
  rw [map_mul]
  rfl

def finiteOrbitRepresentation (U : G →* (E →L[ℝ] E)) (x : E) :
    G →* (finiteOrbitSpan U x →L[ℝ] finiteOrbitSpan U x) where
  toFun g := (U g).restrict (finiteOrbitSpan_invariant U x g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    change U 1 (y : E) = y
    simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    change U (g * h) (y : E) = U g (U h (y : E))
    rw [map_mul]
    rfl

theorem finiteOrbitRepresentation_coe (U : G →* (E →L[ℝ] E)) (x : E)
    (g : G) (y : finiteOrbitSpan U x) :
    (finiteOrbitRepresentation U x g y : E) = U g (y : E) := rfl

theorem finiteOrbitRepresentation_inner (U : G →* (E →L[ℝ] E)) (x : E)
    (hU : ∀ g y z, inner ℝ (U g y) (U g z) = inner ℝ y z)
    (g : G) (y z : finiteOrbitSpan U x) :
    inner ℝ (finiteOrbitRepresentation U x g y) (finiteOrbitRepresentation U x g z) = inner ℝ y z :=
  hU g y z

theorem finiteOrbitRepresentation_average_coe (U : G →* (E →L[ℝ] E)) (x : E)
    (y : finiteOrbitSpan U x) :
    (finiteUnitaryAverage (finiteOrbitRepresentation U x) y : E) = finiteUnitaryAverage U (y : E) := by
  change (finiteOrbitSpan U x).subtypeL (finiteUnitaryAverage (finiteOrbitRepresentation U x) y) = _
  rw [finiteUnitaryAverage_apply, map_smul, map_sum, finiteUnitaryAverage_apply]
  rfl

end RepulsiveCoulomb
