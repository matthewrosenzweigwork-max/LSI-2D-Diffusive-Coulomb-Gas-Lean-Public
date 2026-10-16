module

public import LeanResearch.RepulsiveCoulomb.TriangularContourEdgeCarrier
public import LeanResearch.RepulsiveCoulomb.PointLengthMeasure

@[expose] public section

/-! Exact raw weighted Hausdorff length of each nonexceptional interpolant level,
counting each actual unoriented contour edge exactly once. -/
noncomputable section
open Set MeasureTheory AffineMap
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def gridContourWeightedLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : ℝ :=
  ∑ e : GridContourEdge v t, rawPointSegmentLength a y (gridContourEdgeStart v t e) (gridContourEdgeEnd v t e)

theorem gridContourWeightedLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : 0 ≤ gridContourWeightedLength a y v t := by
  exact Finset.sum_nonneg (fun e _ => rawPointSegmentLength_nonneg a y _ _)

theorem gridContour_weighted_length_sum {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    rawPointLengthMeasure a y ((triangularGridInterpolant v) ⁻¹' {t}) =
      ∑ e : GridContourEdge v t,
        ENNReal.ofReal (rawPointSegmentLength a y (gridContourEdgeStart v t e) (gridContourEdgeEnd v t e)) := by
  rw [← gridContourCarrier_eq_level v ht, gridContourCarrier_eq_edge_union]
  have h := rawPointLengthMeasure_finite_edges ha y
    (gridContourEdgeStart v t) (gridContourEdgeEnd v t) (gridContourEdge_nondegenerate v t)
    (fun e f hef => by
      simpa only [← segment_eq_image_lineMap] using gridContourEdges_intersection_finite v ht e f hef)
  simpa only [← segment_eq_image_lineMap] using h

theorem gridContour_weighted_length_exact {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    rawPointLengthMeasure a y ((triangularGridInterpolant v) ⁻¹' {t}) =
      ENNReal.ofReal (gridContourWeightedLength a y v t) := by
  rw [gridContour_weighted_length_sum ha y v ht, gridContourWeightedLength,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => rawPointSegmentLength_nonneg a y _ _)]

theorem gridContour_weighted_length_finite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) :
    rawPointLengthMeasure a y ((triangularGridInterpolant v) ⁻¹' {t}) ≠ ⊤ := by
  rw [gridContour_weighted_length_exact ha y v ht]
  exact ENNReal.ofReal_ne_top

end RepulsiveCoulomb
