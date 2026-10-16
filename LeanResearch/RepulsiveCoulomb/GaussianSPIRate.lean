import LeanResearch.RepulsiveCoulomb.SuperPoincareAbsorption

/-! Polynomial small-parameter costs are absorbed into the Gaussian SPI rate. -/
noncomputable section
namespace RepulsiveCoulomb

theorem spi_parameter_power_le_exp {s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η) :
    (s / 16) ^ (-η) ≤ (16 : ℝ) ^ η * Real.exp (η / s) := by
  have hl : Real.log s⁻¹ ≤ s⁻¹ := by
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hs)]
  have hp : (s⁻¹) ^ η ≤ Real.exp (η / s) := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr hs)]
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hl hη
  rw [Real.rpow_neg_eq_inv_rpow, inv_div, div_eq_mul_inv,
    Real.mul_rpow (by norm_num) (inv_nonneg.mpr hs.le)]
  exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) _)

theorem gaussian_spi_radius_rate {A B L R s η : ℝ} (hA : 0 ≤ A) (hs : 0 < s)
    (hη : 0 ≤ η) (hR : R ^ 2 = L / s) :
    4 * (A * Real.exp (B * (3 * R) ^ 2) * (s / 16) ^ (-η)) ≤
      (4 * A * (16 : ℝ) ^ η) * Real.exp ((9 * B * L + η) / s) := by
  have h := mul_le_mul_of_nonneg_left (spi_parameter_power_le_exp hs hη)
    (mul_nonneg hA (Real.exp_pos (B * (3 * R) ^ 2)).le)
  have hid : 4 * (A * Real.exp (B * (3 * R) ^ 2) * ((16 : ℝ) ^ η * Real.exp (η / s))) =
      (4 * A * (16 : ℝ) ^ η) * Real.exp ((9 * B * L + η) / s) := by
    calc
      _ = (4 * A * (16 : ℝ) ^ η) * (Real.exp (B * (3 * R) ^ 2) * Real.exp (η / s)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        rw [mul_pow, hR]
        ring
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)).trans_eq hid

end RepulsiveCoulomb
