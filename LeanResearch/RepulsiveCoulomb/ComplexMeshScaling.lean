import LeanResearch.RepulsiveCoulomb.RawPointWeightGeometry
import LeanResearch.RepulsiveCoulomb.ComplexLipschitzCoarea
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Exact physical gradient and volume scaling on the complex plane, including
all points of a piecewise-linear function. No differentiability assumption is inserted. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem complex_gradient_comp_smul (f : ℂ → ℝ) (h : ℝ) (z : ℂ) :
    gradient (fun w => f (h • w)) z = h • gradient f (h • z) := by
  change (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (fun w => f (h • w)) z) = _
  rw [fderiv_comp_smul, map_smul]
  rfl

theorem complex_gradient_comp_pos_smul_norm (f : ℂ → ℝ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    ‖gradient (fun w => f (h • w)) z‖ = h * ‖gradient f (h • z)‖ := by
  rw [complex_gradient_comp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh]

theorem complex_lintegral_comp_pos_smul (f : ℂ → ℝ≥0∞) {h : ℝ} (hh : 0 < h) :
    (∫⁻ z : ℂ, f (h • z)) = ENNReal.ofReal ((h^2)⁻¹) * ∫⁻ z : ℂ, f z := by
  let e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 h hh.ne')
  have hl := lintegral_map_equiv (μ := (volume : Measure ℂ)) f e.toHomeomorph.toMeasurableEquiv
  change (∫⁻ z : ℂ, f z ∂Measure.map (fun z : ℂ => h • z) volume) = ∫⁻ z : ℂ, f (h • z) at hl
  rw [Measure.map_addHaar_smul volume hh.ne', Complex.finrank_real_complex,
    abs_of_pos (inv_pos.mpr (pow_pos hh 2)), lintegral_smul_measure] at hl
  exact hl.symm

theorem complex_lintegral_pos_smul_substitution (f : ℂ → ℝ≥0∞) {h : ℝ} (hh : 0 < h) :
    (∫⁻ z : ℂ, f z) = ENNReal.ofReal (h^2) * ∫⁻ z : ℂ, f (h • z) := by
  rw [complex_lintegral_comp_pos_smul f hh, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg h), mul_inv_cancel₀ (pow_ne_zero 2 hh.ne'),
    ENNReal.ofReal_one, one_mul]

theorem complex_pos_smul_preimage_ball {h : ℝ} (hh : 0 < h) (c : ℂ) (R : ℝ) :
    (fun z : ℂ => h • z) ⁻¹' ball c R = ball (h⁻¹ • c) (R/h) := by
  ext z
  change dist (h • z) c < R ↔ dist z (h⁻¹ • c) < R/h
  have he : h • z - c = h • (z - h⁻¹ • c) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos hh,dist_eq_norm,lt_div_iff₀ hh]
  constructor <;> intro hz <;> nlinarith

theorem complex_ball_lintegral_pos_smul (f : ℂ → ℝ≥0∞) {h : ℝ} (hh : 0 < h) (c : ℂ) (R : ℝ) :
    (∫⁻ z in ball c R, f z) =
      ENNReal.ofReal (h^2) * ∫⁻ z in ball (h⁻¹ • c) (R/h), f (h • z) := by
  rw [← lintegral_indicator isOpen_ball.measurableSet,
    complex_lintegral_pos_smul_substitution _ hh,
    ← lintegral_indicator isOpen_ball.measurableSet]
  congr 1
  apply lintegral_congr
  intro z
  have hb : h • z ∈ ball c R ↔ z ∈ ball (h⁻¹ • c) (R/h) := by
    change z ∈ (fun z : ℂ => h • z) ⁻¹' ball c R ↔ _
    rw [complex_pos_smul_preimage_ball hh]
  by_cases hz : z ∈ ball (h⁻¹ • c) (R/h)
  · rw [Set.indicator_of_mem (hb.mpr hz), Set.indicator_of_mem hz]
  · have hh' : h • z ∉ ball c R := fun h => hz (hb.mp h)
    rw [Set.indicator_of_notMem hh', Set.indicator_of_notMem hz]

end RepulsiveCoulomb
