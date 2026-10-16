import LeanResearch.RepulsiveCoulomb.CoulombDensityGlobal

/-! RECORDS-ONLY UNCHECKED DRAFT. Actual Gaussian exponential moment of the
literal normalized labeled Gibbs law. No uniformity in N is asserted. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem coulombDensity_le_globalGaussian {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (z : CoulombConfig N) : coulombDensity N β z ≤
      coulombDensityGlobalBound N β * Real.exp (-(β / 4) * ‖z‖ ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (coulombWeight_le_gaussian hβ z)
    (inv_pos.mpr (coulombWeight_integral_pos (N := N) hβ)).le
  simpa only [coulombDensity, coulombDensityGlobalBound, mul_assoc] using h

theorem coulombDensity_mul_exp_quadratic_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : CoulombConfig N =>
      coulombDensity N β z * Real.exp ((β / 8) * ‖z‖ ^ 2)) := by
  refine ((integrable_coulomb_gaussian N (by positivity : 0 < β / 8)).const_mul
    (coulombDensityGlobalBound N β)).mono' ?_ ?_
  · exact ((coulombDensity_continuous hβ.le).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (coulombDensity_nonneg β z) (Real.exp_pos _).le)]
    calc
      _ ≤ (coulombDensityGlobalBound N β * Real.exp (-(β / 4) * ‖z‖ ^ 2)) *
          Real.exp ((β / 8) * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (coulombDensity_le_globalGaussian hβ z) (Real.exp_pos _).le
      _ = coulombDensityGlobalBound N β * Real.exp (-(β / 8) * ‖z‖ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring

theorem coulombMeasure_exp_quadratic_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : CoulombConfig N => Real.exp ((β / 8) * ‖z‖ ^ 2))
      (coulombMeasure N β) := by
  rw [coulombMeasure_eq_withDensity hβ]
  apply (integrable_withDensity_iff_integrable_smul'
    (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (coulombDensity_nonneg (N := N) β _), smul_eq_mul] using
    coulombDensity_mul_exp_quadratic_integrable (N := N) hβ

end RepulsiveCoulomb
