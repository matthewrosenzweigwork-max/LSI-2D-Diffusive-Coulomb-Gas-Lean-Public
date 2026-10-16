import LeanResearch.RepulsiveCoulomb.TriangularContourJordanPartition
import LeanResearch.RepulsiveCoulomb.TriangularContourWeightedLength

/-! Exact additivity of the physical raw weighted length over the finite,
pairwise-disjoint polygonal Jordan component partition. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem gridContourComponentCarrier_compact (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (c : (gridContourGraph v t).ConnectedComponent) :
    IsCompact (gridContourComponentCarrier v t c) := by
  apply isCompact_iUnion
  intro e
  apply isCompact_iUnion
  intro _
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem gridContourComponentCarrier_subset_level (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    gridContourComponentCarrier v t c ⊆ (triangularGridInterpolant v) ⁻¹' {t} := by
  rw [← gridContourCarrier_eq_level v ht, ← gridContourComponentCarrier_union]
  exact subset_iUnion _ c

theorem gridContour_component_length_additive {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v) :
    rawPointLengthMeasure a y ((triangularGridInterpolant v) ⁻¹' {t}) =
      ∑' c : (gridContourGraph v t).ConnectedComponent,
        rawPointLengthMeasure a y (gridContourComponentCarrier v t c) := by
  rw [← gridContourCarrier_eq_level v ht, ← gridContourComponentCarrier_union]
  exact measure_iUnion (gridContourComponentCarrier_disjoint v ht)
    (fun c => (gridContourComponentCarrier_compact v t c).measurableSet)

theorem gridContour_component_length_finite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : (gridContourGraph v t).ConnectedComponent) :
    rawPointLengthMeasure a y (gridContourComponentCarrier v t c) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (gridContour_weighted_length_finite ha y v ht)
    (measure_mono (gridContourComponentCarrier_subset_level v ht c))

def gridContourComponentWeightedLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (c : (gridContourGraph v t).ConnectedComponent) : ℝ :=
  (rawPointLengthMeasure a y).real (gridContourComponentCarrier v t c)

theorem gridContourComponentWeightedLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (c : (gridContourGraph v t).ConnectedComponent) :
    0 ≤ gridContourComponentWeightedLength a y v t c := ENNReal.toReal_nonneg

theorem gridContour_component_length_exact {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    (∑' c : (gridContourGraph v t).ConnectedComponent,
      ENNReal.ofReal (gridContourComponentWeightedLength a y v t c)) =
      ENNReal.ofReal (gridContourWeightedLength a y v t) := by
  have hc : ∀ c, ENNReal.ofReal (gridContourComponentWeightedLength a y v t c) =
      rawPointLengthMeasure a y (gridContourComponentCarrier v t c) := by
    intro c
    exact ENNReal.ofReal_toReal (gridContour_component_length_finite ha y v ht c)
  simp_rw [hc]
  rw [← gridContour_component_length_additive a y v ht, gridContour_weighted_length_exact ha y v ht]

end RepulsiveCoulomb
