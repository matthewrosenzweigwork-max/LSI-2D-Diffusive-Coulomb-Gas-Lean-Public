import LeanResearch.RepulsiveCoulomb.TriangularContourSelectedArea

/-! Actual configuration-uniform localized relative isoperimetry for regular
finite-grid levels. R>=16 is solely the unit-mesh approximation-stage condition. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def pointGridRelativeIsoperimetricConstant (Q : ℝ) : ℝ :=
  Real.pi * Real.exp (8 * Q) + pointWeightedChainCrossingConstant Q

theorem pointGridRelativeIsoperimetricConstant_pos (Q : ℝ) :
    0 < pointGridRelativeIsoperimetricConstant Q := by
  unfold pointGridRelativeIsoperimetricConstant
  exact add_pos (by positivity) (pointWeightedChainCrossingConstant_pos Q)

theorem gridContour_relative_isoperimetry {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (x : ℂ) {R : ℝ} (hR : 16 ≤ R) :
    min ((rawPointMeasure (fun j => 2*a j) y).real
      (ball x R ∩ {z | triangularGridInterpolant v z < t}))
      ((rawPointMeasure (fun j => 2*a j) y).real
      (ball x R ∩ {z | t < triangularGridInterpolant v z})) ≤
    pointGridRelativeIsoperimetricConstant Q * gridContourLocalWeightedLength a y v t x (2*R)^2 := by
  classical
  have hRpos : 0 < R := by linarith
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hCarea : Real.pi * Real.exp (8*Q) ≤ pointGridRelativeIsoperimetricConstant Q := by
    unfold pointGridRelativeIsoperimetricConstant
    linarith [(pointWeightedChainCrossingConstant_pos Q).le]
  have hCcross : pointWeightedChainCrossingConstant Q ≤ pointGridRelativeIsoperimetricConstant Q := by
    unfold pointGridRelativeIsoperimetricConstant
    have h : 0 ≤ Real.pi * Real.exp (8*Q) := by positivity
    linarith
  by_cases hcross : ∃ c : (gridContourGraph v t).ConnectedComponent,
      (gridContourComponentCarrier v t c ∩ ball x R).Nonempty ∧
      ¬ gridContourComponentCarrier v t c ⊆ ball x (2*R)
  · obtain ⟨c,hm,hf⟩ := hcross
    have harea := gridContour_crossing_component_area ha hQ y v ht c x hR hm hf
    have hsub : (rawPointMeasure (fun j => 2*a j) y).real
        (ball x R ∩ {z | triangularGridInterpolant v z < t}) ≤
        (rawPointMeasure (fun j => 2*a j) y).real (ball x R) :=
      measureReal_mono inter_subset_left (rawPointMeasure_ball_lt_top ha2 y x R).ne
    exact (min_le_left _ _).trans (hsub.trans
      (harea.trans (mul_le_mul_of_nonneg_right hCcross (sq_nonneg _))))
  · letI : Fintype (gridContourGraph v t).ConnectedComponent := Fintype.ofFinite _
    let s := Finset.univ.filter (fun c : (gridContourGraph v t).ConnectedComponent =>
      (gridContourComponentCarrier v t c ∩ ball x R).Nonempty)
    have hball : ∀ c ∈ s, gridContourComponentCarrier v t c ⊆ ball x (2*R) := by
      intro c hc
      by_contra h
      exact hcross ⟨c,(Finset.mem_filter.mp hc).2,h⟩
    have hunion : (⋃ c : (gridContourGraph v t).ConnectedComponent,
        ⋃ (_ : (gridContourComponentCarrier v t c ∩ ball x R).Nonempty), gridContourComponentInterior v t c) =
        ⋃ c ∈ s, gridContourComponentInterior v t c := by
      ext z
      simp [s]
    rcases gridContour_relative_sign_cover v ht (isConnected_ball hRpos) with hlo | hhi
    · rw [hunion] at hlo
      have harea := gridContour_selected_area_local ha hQ y v ht s x (2*R) hball hlo
      exact (min_le_left _ _).trans (harea.trans (mul_le_mul_of_nonneg_right hCarea (sq_nonneg _)))
    · rw [hunion] at hhi
      have harea := gridContour_selected_area_local ha hQ y v ht s x (2*R) hball hhi
      exact (min_le_right _ _).trans (harea.trans (mul_le_mul_of_nonneg_right hCarea (sq_nonneg _)))

end RepulsiveCoulomb
