import LeanResearch.RepulsiveCoulomb.TriangularContourCrossingPrefix
import LeanResearch.RepulsiveCoulomb.PointWeightedCrossingChain

/-! Physical local contour length and the actual crossing-component relative
area estimate for the unit-mesh approximation stage. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def gridContourLocalWeightedLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (c : ℂ) (R : ℝ) : ℝ :=
  (rawPointLengthMeasure a y).real (ball c R ∩ (triangularGridInterpolant v) ⁻¹' {t})

theorem gridContourLocalWeightedLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (c : ℂ) (R : ℝ) :
    0 ≤ gridContourLocalWeightedLength a y v t c R := ENNReal.toReal_nonneg

theorem gridContour_local_length_measure_finite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (c : ℂ) (R : ℝ) :
    rawPointLengthMeasure a y (ball c R ∩ (triangularGridInterpolant v) ⁻¹' {t}) ≠ ⊤ :=
  measure_ne_top_of_subset inter_subset_right (gridContour_weighted_length_finite ha y v ht)

theorem gridContourWalk_length_le_local {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {u z : GridContourVertex v t}
    (w : (gridContourGraph v t).Walk u z) (hw : w.IsTrail) (c : ℂ) (R : ℝ)
    (hball : gridContourWalkCarrier v t w ⊆ ball c R) :
    rawPointChainLength a y (fun i => gridContourPosition v t (w.getVert i)) w.length ≤
      gridContourLocalWeightedLength a y v t c R := by
  have hsub : gridContourWalkCarrier v t w ⊆ ball c R ∩ (triangularGridInterpolant v) ⁻¹' {t} :=
    subset_inter hball (gridContourWalkCarrier_subset_level v ht w)
  have h := ENNReal.toReal_mono (gridContour_local_length_measure_finite ha y v ht c R) (measure_mono hsub)
  rw [gridContourWalk_weighted_length ha y v ht w hw,
    ENNReal.toReal_ofReal (rawPointChainLength_nonneg a y _ _)] at h
  exact h

theorem gridContour_crossing_component_area {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (c : (gridContourGraph v t).ConnectedComponent) (x : ℂ) {R : ℝ} (hR : 16 ≤ R)
    (hmeet : (gridContourComponentCarrier v t c ∩ ball x R).Nonempty)
    (hfar : ¬ gridContourComponentCarrier v t c ⊆ ball x (2 * R)) :
    (rawPointMeasure (fun j => 2 * a j) y).real (ball x R) ≤
      pointWeightedChainCrossingConstant Q * gridContourLocalWeightedLength a y v t x (2 * R) ^ 2 := by
  obtain ⟨u,z,w,hw,hstart,hsep,hball⟩ := gridContourComponent_crossing_prefix v ht c x hR hmeet hfar
  have harea := pointSquaredBallArea_le_crossingChainLength_sq ha hQ y
    (fun i => gridContourPosition v t (w.getVert i)) w.length x (by linarith : 0 < R)
    (by simpa using hstart) (by simpa using hsep)
  have hlen := gridContourWalk_length_le_local ha y v ht w hw.isTrail x (2*R) hball
  have hlen0 := rawPointChainLength_nonneg a y (fun i => gridContourPosition v t (w.getVert i)) w.length
  have hs : rawPointChainLength a y (fun i => gridContourPosition v t (w.getVert i)) w.length ^ 2 ≤
      gridContourLocalWeightedLength a y v t x (2 * R) ^ 2 := by nlinarith
  exact harea.trans (mul_le_mul_of_nonneg_left hs (pointWeightedChainCrossingConstant_pos Q).le)

end RepulsiveCoulomb
