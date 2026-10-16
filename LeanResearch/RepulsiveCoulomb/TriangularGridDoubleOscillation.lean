module

public import LeanResearch.RepulsiveCoulomb.TriangularContourLevelProduct
public import LeanResearch.RepulsiveCoulomb.DoubleLayerCake
public import LeanResearch.RepulsiveCoulomb.ComplexLipschitzCoarea

@[expose] public section

/-! The actual unit-grid double-oscillation estimate, obtained from the proved
relative separator by strict double layer cake and physical-gradient coarea.
Mesh scaling and the C1 limit are separate remaining obligations. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem gridContour_local_length_coarea {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : (ℤ × ℤ) →₀ ℝ) (x : ℂ) (R : ℝ) :
    (∫⁻ t : ℝ, rawPointLengthMeasure a y (ball x R ∩ (triangularGridInterpolant v) ⁻¹' {t})) =
      ∫⁻ z in ball x R, ENNReal.ofReal ‖gradient (triangularGridInterpolant v) z‖ *
        ENNReal.ofReal (rawPointWeight a y z) := by
  have hw : Measurable (fun z => ENNReal.ofReal (rawPointWeight a y z)) :=
    ENNReal.measurable_ofReal.comp (rawPointWeight_continuous ha y).measurable
  rw [triangularGridInterpolant_weighted_coarea v _ hw isOpen_ball.measurableSet]
  apply lintegral_congr
  intro t
  exact withDensity_apply _ (isOpen_ball.measurableSet.inter
    ((triangularGridInterpolant_lipschitz v).continuous.measurable (measurableSet_singleton t)))

theorem triangularGrid_double_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) (x : ℂ) {R : ℝ} (hR : 16 ≤ R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |triangularGridInterpolant v q.1 - triangularGridInterpolant v q.2| ∂ν.prod ν) ≤
      2 * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) *
        ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient (triangularGridInterpolant v) z‖ *
          ENNReal.ofReal (rawPointWeight a y z) := by
  let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
  let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
  let K := M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  letI : IsFiniteMeasure ν := ⟨by
    change (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact rawPointMeasure_ball_lt_top ha2 y x R⟩
  have hf := (triangularGridInterpolant_lipschitz v).continuous.measurable
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |triangularGridInterpolant v q.1 - triangularGridInterpolant v q.2| ∂ν.prod ν) ≤
    2 * ENNReal.ofReal K * _
  rw [double_layer_cake_prod hf ν]
  have hae : ∀ᵐ t : ℝ ∂volume, t ∉ gridExceptionalLevels v :=
    (gridExceptionalLevels v).finite_toSet.countable.ae_notMem volume
  have hbound : (∫⁻ t : ℝ, ν {z | triangularGridInterpolant v z < t} * ν {z | t < triangularGridInterpolant v z}) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal K * rawPointLengthMeasure a y
        (ball x (2*R) ∩ (triangularGridInterpolant v) ⁻¹' {t}) := by
    apply lintegral_mono_ae
    filter_upwards [hae] with t ht
    exact gridContour_level_product_bound ha hQ y v ht x hR
  calc
    _ ≤ 2 * ∫⁻ t : ℝ, ENNReal.ofReal K * rawPointLengthMeasure a y
        (ball x (2*R) ∩ (triangularGridInterpolant v) ⁻¹' {t}) := by gcongr
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, gridContour_local_length_coarea ha y v x (2*R)]
      rw [mul_assoc]

end RepulsiveCoulomb
