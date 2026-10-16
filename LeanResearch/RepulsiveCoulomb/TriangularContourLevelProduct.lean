module

public import LeanResearch.RepulsiveCoulomb.TriangularContourRelativeIsoperimetry
public import LeanResearch.RepulsiveCoulomb.RelativeLevelProductBound

@[expose] public section

/-! Actual regular-level product bound in the ENNReal form needed by Tonelli,
with the literal restricted squared-point-weight measure. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem gridContour_level_product_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ} (ht : t ∉ gridExceptionalLevels v)
    (x : ℂ) {R : ℝ} (hR : 16 ≤ R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    ν {z | triangularGridInterpolant v z < t} * ν {z | t < triangularGridInterpolant v z} ≤
      ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) *
        rawPointLengthMeasure a y (ball x (2*R) ∩ (triangularGridInterpolant v) ⁻¹' {t}) := by
  let μ := rawPointMeasure (fun j => 2*a j) y
  let A := ball x R ∩ {z | triangularGridInterpolant v z < t}
  let B := ball x R ∩ {z | t < triangularGridInterpolant v z}
  let M := μ.real (ball x R)
  let K := M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hMfin : μ (ball x R) ≠ ⊤ := (rawPointMeasure_ball_lt_top ha2 y x R).ne
  have hAfin : μ A ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hMfin
  have hBfin : μ B ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hMfin
  have hAM : μ.real A ≤ M := measureReal_mono inter_subset_left hMfin
  have hBM : μ.real B ≤ M := measureReal_mono inter_subset_left hMfin
  have hA0 : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ μ.real B := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := mul_nonneg hM0 (Real.sqrt_nonneg _)
  have hiso := gridContour_relative_isoperimetry ha hQ y v ht x hR
  have hp := relative_level_product_bound hA0 hB0 hM0
    (pointGridRelativeIsoperimetricConstant_pos Q).le
    (gridContourLocalWeightedLength_nonneg a y v t x (2*R)) hAM hBM hiso
  have hf := (triangularGridInterpolant_lipschitz v).continuous.measurable
  change (μ.restrict (ball x R)) {z | triangularGridInterpolant v z < t} *
      (μ.restrict (ball x R)) {z | t < triangularGridInterpolant v z} ≤ ENNReal.ofReal K * _
  rw [Measure.restrict_apply (measurableSet_lt hf measurable_const),
    Measure.restrict_apply (measurableSet_lt measurable_const hf)]
  rw [inter_comm {z | triangularGridInterpolant v z < t}, inter_comm {z | t < triangularGridInterpolant v z}]
  change μ A * μ B ≤ _
  calc
    μ A * μ B = ENNReal.ofReal (μ.real A * μ.real B) := by
      rw [ENNReal.ofReal_mul hA0, Measure.real, Measure.real,
        ENNReal.ofReal_toReal hAfin, ENNReal.ofReal_toReal hBfin]
    _ ≤ ENNReal.ofReal (K * gridContourLocalWeightedLength a y v t x (2*R)) := ENNReal.ofReal_le_ofReal hp
    _ = _ := by
      rw [ENNReal.ofReal_mul hK0]
      congr 1
      exact ENNReal.ofReal_toReal (gridContour_local_length_measure_finite ha y v ht x (2*R))

end RepulsiveCoulomb
