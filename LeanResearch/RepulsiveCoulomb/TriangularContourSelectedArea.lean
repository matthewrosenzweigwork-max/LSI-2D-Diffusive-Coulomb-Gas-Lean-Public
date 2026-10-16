module

public import LeanResearch.RepulsiveCoulomb.TriangularContourLocalLength

@[expose] public section

/-! Weighted area and exact local boundary-length accounting for any finite
selection of actual contour interiors. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal Function
namespace RepulsiveCoulomb

theorem rawPointMeasure_bounded_ne_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {S : Set ℂ} (hS : Bornology.IsBounded S) :
    rawPointMeasure a y S ≠ ⊤ := by
  obtain ⟨R,hR⟩ := hS.subset_closedBall (0 : ℂ)
  exact measure_ne_top_of_subset hR (rawPointMeasure_closedBall_lt_top ha y 0 R).ne

theorem gridContour_selected_length_le_local {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (s : Finset (gridContourGraph v t).ConnectedComponent)
    (x : ℂ) (R : ℝ) (hball : ∀ c ∈ s, gridContourComponentCarrier v t c ⊆ ball x R) :
    (∑ c ∈ s, gridContourComponentWeightedLength a y v t c) ≤
      gridContourLocalWeightedLength a y v t x R := by
  have hd : (s : Set (gridContourGraph v t).ConnectedComponent).Pairwise
      (Disjoint on gridContourComponentCarrier v t) := by
    intro c _ d _ hcd
    exact gridContourComponentCarrier_disjoint v ht hcd
  have heq := measureReal_biUnion_finset (μ := rawPointLengthMeasure a y) hd
    (fun c _ => (gridContourComponentCarrier_compact v t c).measurableSet)
    (fun c _ => gridContour_component_length_finite ha y v ht c)
  change (rawPointLengthMeasure a y).real (⋃ c ∈ s, gridContourComponentCarrier v t c) =
    ∑ c ∈ s, gridContourComponentWeightedLength a y v t c at heq
  rw [← heq]
  apply measureReal_mono ?_ (gridContour_local_length_measure_finite ha y v ht x R)
  intro z hz
  obtain ⟨c,hz⟩ := mem_iUnion.mp hz
  obtain ⟨hc,hz⟩ := mem_iUnion.mp hz
  exact ⟨hball c hc hz,gridContourComponentCarrier_subset_level v ht c hz⟩

theorem gridContour_selected_interior_area {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (s : Finset (gridContourGraph v t).ConnectedComponent) :
    (rawPointMeasure (fun j => 2 * a j) y).real (⋃ c ∈ s, gridContourComponentInterior v t c) ≤
      Real.pi * Real.exp (8 * Q) * (∑ c ∈ s, gridContourComponentWeightedLength a y v t c) ^ 2 := by
  calc
    _ ≤ ∑ c ∈ s, (rawPointMeasure (fun j => 2*a j) y).real (gridContourComponentInterior v t c) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ s, Real.pi * Real.exp (8*Q) * gridContourComponentWeightedLength a y v t c ^ 2 :=
      Finset.sum_le_sum (fun c _ => gridContourComponentInterior_weighted_area ha hQ y v ht c)
    _ = Real.pi * Real.exp (8*Q) * ∑ c ∈ s, gridContourComponentWeightedLength a y v t c ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun c _ => gridContourComponentWeightedLength_nonneg a y v t c)) (by positivity)

theorem gridContour_selected_area_local {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (s : Finset (gridContourGraph v t).ConnectedComponent) (x : ℂ) (R : ℝ)
    (hball : ∀ c ∈ s, gridContourComponentCarrier v t c ⊆ ball x R)
    {S : Set ℂ} (hS : S ⊆ ⋃ c ∈ s, gridContourComponentInterior v t c) :
    (rawPointMeasure (fun j => 2 * a j) y).real S ≤
      Real.pi * Real.exp (8 * Q) * gridContourLocalWeightedLength a y v t x R ^ 2 := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hfin : rawPointMeasure (fun j => 2*a j) y (⋃ c ∈ s, gridContourComponentInterior v t c) ≠ ⊤ := by
    exact measure_biUnion_ne_top s.finite_toSet
      (fun c _ => rawPointMeasure_bounded_ne_top ha2 y (gridContourComponentInterior_bounded v ht c))
  have hm := measureReal_mono hS hfin
  have harea := gridContour_selected_interior_area ha hQ y v ht s
  have hlen := gridContour_selected_length_le_local ha y v ht s x R hball
  have hlen0 : 0 ≤ ∑ c ∈ s, gridContourComponentWeightedLength a y v t c :=
    Finset.sum_nonneg (fun c _ => gridContourComponentWeightedLength_nonneg a y v t c)
  have hs : (∑ c ∈ s, gridContourComponentWeightedLength a y v t c)^2 ≤
      gridContourLocalWeightedLength a y v t x R ^ 2 := by nlinarith
  exact hm.trans (harea.trans (mul_le_mul_of_nonneg_left hs (by positivity)))

end RepulsiveCoulomb
