import LeanResearch.RepulsiveCoulomb.PointMetricMapJacobian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sharp planar outer distortion from the actual metric bounds

Draft, not compiled or accepted. The plane is `ℂ` with its usual Euclidean norm,
regarded as a real inner product space. The real adjoint, rather than an
arbitrary matrix norm or a complex-linear adjoint, is essential here.

The two-dimensional cofactor identity `A J A† = det(A) J`, where `J z = I * z`,
turns the lower stretch bound into `c * ‖A‖ ≤ |det A|`. Combining this with the
upper stretch bound gives outer distortion `L²`, including zero density. No
division by the density or determinant, singular-value witnesses, or inverse
map is needed.

The final statements retain `|det|`. They do not construct the metric map,
prove its orientation, establish positive signed Jacobian, or construct weak
derivatives / Sobolev membership.
-/

noncomputable section
open Set MeasureTheory

namespace RepulsiveCoulomb

private theorem complex_continuousLinear_apply_reIm (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = z.re • A 1 + z.im • A Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- The planar cofactor identity, with the genuine real Hilbert-space adjoint.
No invertibility or determinant-sign hypothesis is needed. -/
theorem complex_continuousLinear_mul_I_adjoint (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A (Complex.I * A.adjoint z) =
      (A.toLinearMap.det : ℂ) * (Complex.I * z) := by
  have hre : (A.adjoint z).re = (A 1).re * z.re + (A 1).im * z.im := by
    have h := A.adjoint_inner_right (1 : ℂ) z
    simpa [Complex.inner, Complex.mul_re, mul_comm] using h
  have him : (A.adjoint z).im =
      (A Complex.I).re * z.re + (A Complex.I).im * z.im := by
    have h := A.adjoint_inner_right Complex.I z
    simpa [Complex.inner, Complex.mul_re, mul_comm] using h
  rw [complex_continuousLinear_apply_reIm]
  rw [complex_realLinear_det_formula]
  apply Complex.ext <;>
    simp only [ContinuousLinearMap.coe_coe, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, hre, him] <;> ring

/-- In the Euclidean plane, a lower stretch bound controls the product of
that lower stretch and the operator norm by the absolute determinant. This is
the mixed estimate lost when one only combines independent determinant and
operator-norm bounds. The statement remains true when `c = 0`. -/
theorem complex_continuousLinear_lower_mul_norm_le_abs_det
    (A : ℂ →L[ℝ] ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖) :
    c * ‖A‖ ≤ |A.toLinearMap.det| := by
  have hpoint (v : ℂ) : c * ‖A.adjoint v‖ ≤ |A.toLinearMap.det| * ‖v‖ := by
    have h := hlower (Complex.I * A.adjoint v)
    rw [complex_continuousLinear_mul_I_adjoint] at h
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs] using h
  have hop : ‖c • A.adjoint‖ ≤ |A.toLinearMap.det| := by
    apply (c • A.adjoint).opNorm_le_bound (abs_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc] using hpoint v
  have hadjoint : ‖A.adjoint‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map A
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hadjoint] using hop

/-- Exact planar outer-distortion estimate from symmetric stretch bounds.
Its constant is `L²`, with no strictly-positive-density assumption. -/
theorem complex_continuousLinear_sharp_outer_distortion (A : ℂ →L[ℝ] ℂ)
    {ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 1 ≤ L)
    (hlower : ∀ v : ℂ, ρ / L * ‖v‖ ≤ ‖A v‖)
    (hupper : ∀ v : ℂ, ‖A v‖ ≤ L * ρ * ‖v‖) :
    ‖A‖ ^ 2 ≤ L ^ 2 * |A.toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmix := complex_continuousLinear_lower_mul_norm_le_abs_det A
    (div_nonneg hρ hLp.le) hlower
  have hnorm : ‖A‖ ≤ L * ρ := A.opNorm_le_bound (mul_nonneg hLp.le hρ) hupper
  calc
    ‖A‖ ^ 2 = ‖A‖ * ‖A‖ := by ring
    _ ≤ (L * ρ) * ‖A‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = L ^ 2 * (ρ / L * ‖A‖) := by field_simp [hLp.ne'] <;> ring
    _ ≤ L ^ 2 * |A.toLinearMap.det| :=
      mul_le_mul_of_nonneg_left hmix (sq_nonneg L)

/-- Retain the accepted absolute-determinant comparison and replace only its
outer-distortion conclusion by the sharp planar estimate. -/
theorem complex_continuousLinear_sharp_jacobian_bounds (A : ℂ →L[ℝ] ℂ)
    {ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 1 ≤ L)
    (hlower : ∀ v : ℂ, ρ / L * ‖v‖ ≤ ‖A v‖)
    (hupper : ∀ v : ℂ, ‖A v‖ ≤ L * ρ * ‖v‖) :
    (ρ / L) ^ 2 ≤ |A.toLinearMap.det| ∧
      |A.toLinearMap.det| ≤ (L * ρ) ^ 2 ∧
      ‖A‖ ^ 2 ≤ L ^ 2 * |A.toLinearMap.det| := by
  have hJ := complex_continuousLinear_jacobian_bounds A hρ hL hlower hupper
  exact ⟨hJ.1, hJ.2.1,
    complex_continuousLinear_sharp_outer_distortion A hρ hL hlower hupper⟩

/-- Actual a.e. derivative bounds, with sharp planar outer distortion, for an
already supplied map satisfying the two-sided point-metric inequalities. -/
theorem pointMetricMap_ae_sharp_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {L : ℝ} (hL : 1 ≤ L)
    (hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z))
    (hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / L ^ 2 ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 2 * |(fderiv ℝ F z).toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  filter_upwards [pointMetricMap_ae_differentiableAt ha y hLp.le hupper] with z hz
  have hd (v : ℂ) := pointMetricMap_fderiv_bounds ha y hLp hlower hupper hz v
  have hJ := complex_continuousLinear_sharp_jacobian_bounds (fderiv ℝ F z)
    (pointConformalDensity_nonneg a y z) hL (fun v ↦ (hd v).1) (fun v ↦ (hd v).2)
  simp only [div_pow, mul_pow, pointConformalDensity_sq] at hJ
  exact ⟨hz, hJ⟩

/-- The source-style metric homeomorphism inequalities imply absolute-Jacobian
comparison and outer distortion with the same constant `L²`. -/
theorem pointMetricHomeomorph_ae_sharp_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / L ^ 2 ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 2 * |(fderiv ℝ F z).toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply pointMetricMap_ae_sharp_jacobian_bounds ha y hL
  · intro p z
    have h := mul_le_mul_of_nonneg_left (hmetric p z).1 hLp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hLp.ne', one_mul, dist_eq_norm] using h
  · intro p z
    simpa only [dist_eq_norm] using (hmetric p z).2

/-- Substitution of the sharp metric constant gives both absolute-Jacobian
comparison and outer distortion with `C = K = 1 + q / 2`. Map existence,
orientation / positive signed Jacobian, and Sobolev membership remain separate.
The nonnegative parameter `q` is tied to the metric hypothesis as in the accepted
conditional endpoint; no equality with the total mass is assumed or inferred. -/
theorem pointSharpMetricHomeomorph_ae_sharp_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hmetric : ∀ p z,
      (Real.sqrt (1 + q / 2))⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ Real.sqrt (1 + q / 2) * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / (1 + q / 2) ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ (1 + q / 2) * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ (1 + q / 2) * |(fderiv ℝ F z).toLinearMap.det| := by
  have hc : 0 ≤ 1 + q / 2 := by positivity
  have hL : 1 ≤ Real.sqrt (1 + q / 2) := by
    rw [Real.le_sqrt (by norm_num) hc]
    nlinarith
  have hL2 := Real.sq_sqrt hc
  simpa only [hL2] using pointMetricHomeomorph_ae_sharp_jacobian_bounds ha y F hL hmetric

end RepulsiveCoulomb
