module

public import LeanResearch.RepulsiveCoulomb.TriangularGridPointClassification
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

/-! Actual volume-null grid skeletons, including a countable sequence of meshes.
No union over all real mesh sizes is used. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

theorem complex_affine_fiber_volume_zero (F : ℂ →ᵃ[ℝ] ℝ) (hF : Function.Surjective F) (t : ℝ) :
    volume {z : ℂ | F z = t} = 0 := by
  let S : AffineSubspace ℝ ℂ := ({t} : AffineSubspace ℝ ℝ).comap F
  have hS : S ≠ ⊤ := by
    intro h
    obtain ⟨z,hz⟩ := hF (t+1)
    have hzS : z ∈ S := by rw [h]; trivial
    change F z = t at hzS
    linarith
  exact Measure.addHaar_affineSubspace volume S hS

def gridCoordinate (j : Fin 3) : ℂ →ₗ[ℝ] ℝ :=
  ![Complex.reCLM.toLinearMap, Complex.imCLM.toLinearMap,
    Complex.reCLM.toLinearMap - Complex.imCLM.toLinearMap] j

theorem gridCoordinate_surjective (j : Fin 3) : Function.Surjective (gridCoordinate j) := by
  intro t
  fin_cases j
  · exact ⟨(t : ℂ), by simp [gridCoordinate]⟩
  · exact ⟨⟨0,t⟩, by simp [gridCoordinate]⟩
  · exact ⟨(t : ℂ), by simp [gridCoordinate]⟩

theorem gridCoordinate_fiber_volume_zero (j : Fin 3) (t : ℝ) :
    volume {z : ℂ | gridCoordinate j z = t} = 0 :=
  complex_affine_fiber_volume_zero (gridCoordinate j).toAffineMap (gridCoordinate_surjective j) t

def unitGridSkeleton : Set ℂ := ⋃ k : ℤ, ⋃ j : Fin 3, {z : ℂ | gridCoordinate j z = (k : ℝ)}

theorem unitGridSkeleton_volume_zero : volume unitGridSkeleton = 0 := by
  apply measure_iUnion_null
  intro k
  apply measure_iUnion_null
  intro j
  exact gridCoordinate_fiber_volume_zero j k

def gridSequenceSkeleton (h : ℕ → ℝ) : Set ℂ :=
  ⋃ n : ℕ, ⋃ k : ℤ, ⋃ j : Fin 3, {z : ℂ | gridCoordinate j z = h n * (k : ℝ)}

theorem gridSequenceSkeleton_volume_zero (h : ℕ → ℝ) : volume (gridSequenceSkeleton h) = 0 := by
  apply measure_iUnion_null
  intro n
  apply measure_iUnion_null
  intro k
  apply measure_iUnion_null
  intro j
  exact gridCoordinate_fiber_volume_zero j _

end RepulsiveCoulomb
