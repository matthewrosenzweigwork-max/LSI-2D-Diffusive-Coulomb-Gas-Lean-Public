import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Two-sided norm bounds on a genuine real-linear map of the complex plane
control its actual determinant. This is the linear-algebra input to the
metric-to-Jacobian passage; the Jacobian is never defined to be a density. -/
noncomputable section
namespace RepulsiveCoulomb

theorem complex_realLinear_det_formula (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (star (A 1) * A Complex.I).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem complex_realLinear_abs_det_le_columns (A : ℂ →ₗ[ℝ] ℂ) :
    |A.det| ≤ ‖A 1‖ * ‖A Complex.I‖ := by
  rw [complex_realLinear_det_formula]
  calc
    |(star (A 1) * A Complex.I).im| ≤ ‖star (A 1) * A Complex.I‖ := Complex.abs_im_le_norm _
    _ = ‖A 1‖ * ‖A Complex.I‖ := by
      rw [norm_mul]
      exact congrArg (fun r : ℝ ↦ r * ‖A Complex.I‖) (Complex.norm_conj (A 1))

theorem complex_realLinear_abs_det_upper (A : ℂ →ₗ[ℝ] ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ v : ℂ, ‖A v‖ ≤ C * ‖v‖) : |A.det| ≤ C ^ 2 := by
  have h1 : ‖A 1‖ ≤ C := by simpa only [norm_one, mul_one] using hA 1
  have hI : ‖A Complex.I‖ ≤ C := by simpa only [Complex.norm_I, mul_one] using hA Complex.I
  calc
    |A.det| ≤ ‖A 1‖ * ‖A Complex.I‖ := complex_realLinear_abs_det_le_columns A
    _ ≤ C * C := mul_le_mul h1 hI (norm_nonneg _) hC
    _ = C ^ 2 := by ring

theorem complex_realLinear_abs_det_lower (A : ℂ →ₗ[ℝ] ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hA : ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖) : c ^ 2 ≤ |A.det| := by
  rcases hc.eq_or_lt with hc0 | hc
  · subst c
    simpa only [zero_pow (by decide : 2 ≠ 0)] using abs_nonneg A.det
  · have hAi : Function.Injective A := by
      intro u v huv
      have hz : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
      have hb := hA (u - v)
      rw [hz, norm_zero] at hb
      have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    let e : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective A ⟨hAi, LinearMap.surjective_of_injective hAi⟩
    have hinv (v : ℂ) : ‖e.symm v‖ ≤ c⁻¹ * ‖v‖ := by
      have h := hA (e.symm v)
      change c * ‖e.symm v‖ ≤ ‖e (e.symm v)‖ at h
      rw [e.apply_symm_apply] at h
      have hd : ‖e.symm v‖ ≤ ‖v‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)
      simpa only [div_eq_mul_inv, mul_comm] using hd
    have hdet := complex_realLinear_abs_det_upper (e.symm : ℂ →ₗ[ℝ] ℂ)
      (inv_nonneg.mpr hc.le) hinv
    have hdet' : |(e.symm : ℂ →ₗ[ℝ] ℂ).det| * c ^ 2 ≤ 1 := by
      apply (le_div_iff₀ (sq_pos_of_pos hc)).mp
      simpa only [inv_pow, one_div] using hdet
    have hmul : |A.det| * |(e.symm : ℂ →ₗ[ℝ] ℂ).det| = 1 := by
      rw [← abs_mul]
      have he := e.det_mul_det_symm
      change A.det * (e.symm : ℂ →ₗ[ℝ] ℂ).det = 1 at he
      rw [he, abs_one]
    calc
      c ^ 2 = (|A.det| * |(e.symm : ℂ →ₗ[ℝ] ℂ).det|) * c ^ 2 := by rw [hmul, one_mul]
      _ = |A.det| * (|(e.symm : ℂ →ₗ[ℝ] ℂ).det| * c ^ 2) := by ring
      _ ≤ |A.det| * 1 := mul_le_mul_of_nonneg_left hdet' (abs_nonneg _)
      _ = |A.det| := mul_one _

/-- The absolute Jacobian and analytic outer distortion follow from actual
linear stretch bounds, including the zero-density case. -/
theorem complex_continuousLinear_jacobian_bounds (A : ℂ →L[ℝ] ℂ)
    {ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 1 ≤ L)
    (hlower : ∀ v : ℂ, ρ / L * ‖v‖ ≤ ‖A v‖)
    (hupper : ∀ v : ℂ, ‖A v‖ ≤ L * ρ * ‖v‖) :
    (ρ / L) ^ 2 ≤ |A.toLinearMap.det| ∧ |A.toLinearMap.det| ≤ (L * ρ) ^ 2 ∧
      ‖A‖ ^ 2 ≤ L ^ 4 * |A.toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hl := complex_realLinear_abs_det_lower A.toLinearMap (div_nonneg hρ hLp.le) hlower
  have hu := complex_realLinear_abs_det_upper A.toLinearMap (mul_nonneg hLp.le hρ) hupper
  have hnorm : ‖A‖ ≤ L * ρ := A.opNorm_le_bound (mul_nonneg hLp.le hρ) hupper
  refine ⟨hl, hu, ?_⟩
  have hnorm2 : ‖A‖ ^ 2 ≤ (L * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hl' := mul_le_mul_of_nonneg_left hl (sq_nonneg L)
  have hcancel : L ^ 2 * (ρ / L) ^ 2 = ρ ^ 2 := by field_simp [hLp.ne']
  rw [hcancel] at hl'
  have hfinal := mul_le_mul_of_nonneg_left hl' (sq_nonneg L)
  nlinarith only [hnorm2, hfinal]

end RepulsiveCoulomb
