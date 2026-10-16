import LeanResearch.RepulsiveCoulomb.TriangularContourChainLength
import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.JordanClosed

/-! The actual bounded Jordan interior of each contour component, transported
back to the physical complex plane, with a configuration-uniform weighted area bound. -/
noncomputable section
open Set Schoenflies MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def gridContourComponentInterior (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (c : (gridContourGraph v t).ConnectedComponent) : Set ℂ :=
  Complex.orthonormalBasisOneI.repr ⁻¹'
    inside (Complex.orthonormalBasisOneI.repr '' gridContourComponentCarrier v t c)

theorem gridContourComponentInterior_frontier (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    frontier (gridContourComponentInterior v t c) = gridContourComponentCarrier v t c := by
  let e := Complex.orthonormalBasisOneI.repr.toHomeomorph
  have hs := jordan_curve_theorem (gridContourComponent_isJordan_polygon v ht c).1
  change frontier (e ⁻¹' inside _) = _
  rw [← e.preimage_frontier, hs.frontier_inside]
  exact preimage_image_eq _ e.injective

theorem gridContourComponentInterior_compact_closure (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    IsCompact (closure (gridContourComponentInterior v t c)) := by
  let e := Complex.orthonormalBasisOneI.repr.toHomeomorph
  have hs := jordan_curve_theorem (gridContourComponent_isJordan_polygon v ht c).1
  change IsCompact (closure (e ⁻¹' inside _))
  rw [← e.preimage_closure, ← e.image_symm]
  exact hs.isBounded_inside.isCompact_closure.image e.symm.continuous

theorem gridContourComponentInterior_bounded (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    Bornology.IsBounded (gridContourComponentInterior v t c) :=
  (gridContourComponentInterior_compact_closure v ht c).isBounded.subset subset_closure

theorem gridContourComponentInterior_open_connected (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    IsOpen (gridContourComponentInterior v t c) ∧ IsConnected (gridContourComponentInterior v t c) := by
  let e := Complex.orthonormalBasisOneI.repr.toHomeomorph
  have hs := jordan_curve_theorem (gridContourComponent_isJordan_polygon v ht c).1
  exact ⟨hs.isOpen_inside.preimage e.continuous, e.isConnected_preimage.mpr hs.isConnected_inside⟩

theorem gridContourComponentInterior_weighted_area {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (c : (gridContourGraph v t).ConnectedComponent) :
    (rawPointMeasure (fun j => 2 * a j) y).real (gridContourComponentInterior v t c) ≤
      Real.pi * Real.exp (8 * Q) * gridContourComponentWeightedLength a y v t c ^ 2 := by
  apply gridContourComponent_region_area ha hQ y v ht c (gridContourComponentInterior_bounded v ht c)
  rw [gridContourComponentInterior_frontier v ht c]

end RepulsiveCoulomb
