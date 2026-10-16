import LeanResearch.RepulsiveCoulomb.RawPointMeasureScaling

/-! Exact raw-weighted physical-gradient integral scaling for an arbitrary
observable, including its total Frechet derivative at nonsmooth points. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem complex_scaled_gradient_at_smul (f : ℂ → ℝ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    ‖gradient (fun w => f (h⁻¹ • w)) (h • z)‖ = h⁻¹ * ‖gradient f z‖ := by
  rw [complex_gradient_comp_pos_smul_norm f (inv_pos.mpr hh), smul_smul,inv_mul_cancel₀ hh.ne',one_smul]

theorem rawPoint_scaled_gradient_integrand {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (f : ℂ → ℝ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    ENNReal.ofReal ‖gradient (fun w => f (h⁻¹ • w)) (h • z)‖ * ENNReal.ofReal (rawPointWeight a y (h • z)) =
      ENNReal.ofReal (h⁻¹ * h^(∑ j,a j)) *
        (ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a (fun j => h⁻¹ • y j) z)) := by
  rw [complex_scaled_gradient_at_smul f hh,rawPointWeight_smul_rescaling a y hh,
    ENNReal.ofReal_mul (inv_nonneg.mpr hh.le),
    ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _), ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
  ring

theorem rawPoint_gradient_ball_scaling {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (f : ℂ → ℝ) {h : ℝ} (hh : 0 < h) (c : ℂ) (R : ℝ) :
    (∫⁻ z in ball c R, ENNReal.ofReal ‖gradient (fun w => f (h⁻¹ • w)) z‖ *
      ENNReal.ofReal (rawPointWeight a y z)) =
      ENNReal.ofReal (rawPointLengthScale a h) *
        ∫⁻ z in ball (h⁻¹ • c) (R/h), ENNReal.ofReal ‖gradient f z‖ *
          ENNReal.ofReal (rawPointWeight a (fun j => h⁻¹ • y j) z) := by
  rw [complex_ball_lintegral_pos_smul _ hh c R]
  simp_rw [rawPoint_scaled_gradient_integrand a y f hh]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg h)]
  congr 2
  unfold rawPointLengthScale
  field_simp

end RepulsiveCoulomb
