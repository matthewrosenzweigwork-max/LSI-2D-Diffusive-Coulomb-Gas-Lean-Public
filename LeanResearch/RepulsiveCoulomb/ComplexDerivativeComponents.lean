module

public import LeanResearch.RepulsiveCoulomb.TriangularGridTranslatedDerivative

@[expose] public section

/-! Real-linear derivative control from the two physical complex coordinate directions. -/
noncomputable section
namespace RepulsiveCoulomb

theorem complex_realLinear_decomposition (T : ℂ →L[ℝ] ℝ) (z : ℂ) :
    T z = z.re * T 1 + z.im * T Complex.I := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by apply Complex.ext <;> simp
  have hh := congrArg T hz
  simpa only [map_add,map_smul,smul_eq_mul] using hh.symm

theorem complex_realLinear_norm_le (T : ℂ →L[ℝ] ℝ) : ‖T‖ ≤ |T 1| + |T Complex.I| := by
  apply T.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro z
  rw [Real.norm_eq_abs,complex_realLinear_decomposition]
  calc
    _ ≤ |z.re*T 1| + |z.im*T Complex.I| := by simpa only [Real.norm_eq_abs] using norm_add_le (z.re * T 1) (z.im * T Complex.I)
    _ = |z.re| * |T 1| + |z.im| * |T Complex.I| := by rw [abs_mul,abs_mul]
    _ ≤ ‖z‖ * |T 1| + ‖z‖ * |T Complex.I| :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = _ := by ring

theorem normalized_difference_error {h d L ε : ℝ} (hh : 0 < h)
    (herror : |d-h*L| ≤ ε*h) : |h⁻¹*d-L| ≤ ε := by
  have he : h⁻¹*d-L = (d-h*L)/h := by field_simp
  rw [he,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact herror

theorem complex_gradient_sub_norm (f g : ℂ → ℝ) (z : ℂ) :
    ‖gradient f z - gradient g z‖ = ‖fderiv ℝ f z - fderiv ℝ g z‖ := by
  change ‖(InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z) -
    (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g z)‖ = _
  rw [← map_sub]
  exact (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _

end RepulsiveCoulomb
