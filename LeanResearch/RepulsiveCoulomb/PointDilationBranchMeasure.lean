import LeanResearch.RepulsiveCoulomb.RawPointMeasureScaling
import LeanResearch.RepulsiveCoulomb.PointMeasureParametric

/-! Literal Gaussian point-weight dilation, including the partition factor and
normalized measure. Indexed roots are transported without combining or dropping
coincident roots; all exponents remain unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointDilationBranch_weight {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) (z : ℂ) :
    pointWeight γ a y (h • z) = h ^ (∑ j, a j) *
      pointWeight (γ * h ^ 2) a (fun j => h⁻¹ • y j) z := by
  change Real.exp (-γ * ‖h • z‖ ^ 2 / 2) * rawPointWeight a y (h • z) =
    h ^ (∑ j, a j) * (Real.exp (-(γ * h ^ 2) * ‖z‖ ^ 2 / 2) *
      rawPointWeight a (fun j => h⁻¹ • y j) z)
  rw [rawPointWeight_smul_rescaling a y hh, norm_smul, Real.norm_eq_abs, abs_of_pos hh, mul_pow]
  have he : -γ * (h ^ 2 * ‖z‖ ^ 2) / 2 = -(γ * h ^ 2) * ‖z‖ ^ 2 / 2 := by ring
  rw [he]
  ring

theorem pointDilationBranch_raw_lintegral {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) (F : ℂ → ℝ≥0∞) :
    (∫⁻ z, ENNReal.ofReal (pointWeight γ a y z) * F z) =
      ENNReal.ofReal (h ^ 2 * h ^ (∑ j, a j)) *
        ∫⁻ z, ENNReal.ofReal (pointWeight (γ * h ^ 2) a (fun j => h⁻¹ • y j) z) * F (h • z) := by
  rw [complex_lintegral_pos_smul_substitution _ hh]
  simp_rw [pointDilationBranch_weight γ a y hh,
    ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg h)]

theorem pointDilationBranch_partition {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) :
    pointPartition γ a y = ENNReal.ofReal (h ^ 2 * h ^ (∑ j, a j)) *
      pointPartition (γ * h ^ 2) a (fun j => h⁻¹ • y j) := by
  simpa only [pointPartition, mul_one] using pointDilationBranch_raw_lintegral γ a y hh (fun _ => 1)

theorem pointDilationBranch_lintegral {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂pointMeasure γ a y) =
      ∫⁻ z, F (h • z) ∂pointMeasure (γ * h ^ 2) a (fun j => h⁻¹ • y j) := by
  have hc : 0 < h ^ 2 * h ^ (∑ j, a j) :=
    mul_pos (pow_pos hh 2) (Real.rpow_pos_of_pos hh _)
  have hc0 : ENNReal.ofReal (h ^ 2 * h ^ (∑ j, a j)) ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  rw [pointMeasure_lintegral γ a y hF,
    pointMeasure_lintegral (γ * h ^ 2) a (fun j => h⁻¹ • y j)
      (F := fun z : ℂ => F (h • z)) (hF.comp (continuous_const_smul h).measurable),
    pointDilationBranch_raw_lintegral γ a y hh,
    pointDilationBranch_partition γ a y hh,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top)]
  calc
    _ = (ENNReal.ofReal (h ^ 2 * h ^ (∑ j, a j)))⁻¹ *
        ENNReal.ofReal (h ^ 2 * h ^ (∑ j, a j)) *
        ((pointPartition (γ * h ^ 2) a (fun j => h⁻¹ • y j))⁻¹ *
          ∫⁻ z, ENNReal.ofReal (pointWeight (γ * h ^ 2) a (fun j => h⁻¹ • y j) z) * F (h • z)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]

theorem pointDilationBranch_measurePreserving {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) :
    MeasurePreserving (fun z : ℂ => h • z)
      (pointMeasure (γ * h ^ 2) a (fun j => h⁻¹ • y j)) (pointMeasure γ a y) := by
  refine ⟨(continuous_const_smul h).measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (continuous_const_smul h).measurable]
  exact (pointDilationBranch_lintegral γ a y hh hF).symm

theorem pointDilationBranch_to_unit {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) :
    MeasurePreserving (fun z : ℂ => Real.sqrt γ • z) (pointMeasure γ a y)
      (pointMeasure 1 a (fun j => Real.sqrt γ • y j)) := by
  have hs : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have H := pointDilationBranch_measurePreserving 1 a (fun j => Real.sqrt γ • y j) hs
  simpa only [one_mul, Real.sq_sqrt hγ.le, smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using H

theorem pointDilationBranch_from_unit {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) :
    MeasurePreserving (fun z : ℂ => (Real.sqrt γ)⁻¹ • z)
      (pointMeasure 1 a (fun j => Real.sqrt γ • y j)) (pointMeasure γ a y) := by
  have hs : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have he : γ * ((Real.sqrt γ)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hγ.le, mul_inv_cancel₀ hγ.ne']
  have H := pointDilationBranch_measurePreserving γ a y (inv_pos.mpr hs)
  simpa only [he, inv_inv] using H

end RepulsiveCoulomb
