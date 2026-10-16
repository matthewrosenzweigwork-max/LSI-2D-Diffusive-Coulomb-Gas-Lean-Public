module

public import LeanResearch.RepulsiveCoulomb.ComplexMeshScaling
public import LeanResearch.RepulsiveCoulomb.PointSquaredWeightRadius

@[expose] public section

/-! Exact raw point-weight measure scaling, retaining the literal exponent sum.
No location-separation or uniform approximation hypothesis is introduced. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def rawPointLengthScale {m : ℕ} (a : Fin m → ℝ) (h : ℝ) : ℝ := h * h^(∑ j, a j)

theorem rawPointLengthScale_pos {m : ℕ} (a : Fin m → ℝ) {h : ℝ} (hh : 0 < h) :
    0 < rawPointLengthScale a h := mul_pos hh (Real.rpow_pos_of_pos hh _)

theorem rawPoint_double_measure_scale {m : ℕ} (a : Fin m → ℝ) {h : ℝ} (hh : 0 < h) :
    h^2 * h^(∑ j, 2*a j) = rawPointLengthScale a h ^ 2 := by
  rw [← Finset.mul_sum, mul_comm (2:ℝ) (∑ j, a j), Real.rpow_mul hh.le, Real.rpow_two]
  unfold rawPointLengthScale
  ring

theorem rawPointWeight_smul_rescaling {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) (z : ℂ) :
    rawPointWeight a y (h • z) = h^(∑ j, a j) * rawPointWeight a (fun j => h⁻¹ • y j) z := by
  simpa only [zero_add,sub_zero] using rawPointWeight_affine_rescaling a y 0 hh z

theorem rawPointMeasure_lintegral_smul {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h)
    (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂rawPointMeasure a y) = ENNReal.ofReal (h^2 * h^(∑ j,a j)) *
      ∫⁻ z, F (h • z) ∂rawPointMeasure a (fun j => h⁻¹ • y j) := by
  have hw : Measurable (fun z => ENNReal.ofReal (rawPointWeight a y z)) :=
    ENNReal.measurable_ofReal.comp (rawPointWeight_continuous ha y).measurable
  have hw' : Measurable (fun z => ENNReal.ofReal (rawPointWeight a (fun j => h⁻¹ • y j) z)) :=
    ENNReal.measurable_ofReal.comp (rawPointWeight_continuous ha _).measurable
  have hF' : Measurable (fun z : ℂ => F (h • z)) := hF.comp (continuous_const_smul h).measurable
  rw [rawPointMeasure,rawPointMeasure,
    lintegral_withDensity_eq_lintegral_mul volume hw hF,
    lintegral_withDensity_eq_lintegral_mul volume hw' hF']
  simp only [Pi.mul_apply]
  rw [complex_lintegral_pos_smul_substitution _ hh]
  have hint : (∫⁻ z : ℂ, ENNReal.ofReal (rawPointWeight a y (h • z)) * F (h • z)) =
      ENNReal.ofReal (h^(∑ j,a j)) * ∫⁻ z : ℂ,
        ENNReal.ofReal (rawPointWeight a (fun j => h⁻¹ • y j) z) * F (h • z) := by
    simp_rw [rawPointWeight_smul_rescaling a y hh, ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _), mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hint,← mul_assoc,← ENNReal.ofReal_mul (sq_nonneg h)]

theorem rawPointSquaredMeasure_lintegral_smul {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h)
    (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂rawPointMeasure (fun j => 2*a j) y) = ENNReal.ofReal (rawPointLengthScale a h ^ 2) *
      ∫⁻ z, F (h • z) ∂rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j) := by
  rw [rawPointMeasure_lintegral_smul (fun j => mul_nonneg (by norm_num) (ha j)) y hh F hF,
    rawPoint_double_measure_scale a hh]

end RepulsiveCoulomb
