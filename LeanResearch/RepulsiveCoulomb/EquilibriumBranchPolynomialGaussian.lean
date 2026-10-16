import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit planar Gaussian domination for every real nonnegative polynomial
exponent. This preserves the manuscript's full m>=0 range without restricting
moments to natural powers or introducing a special-function integrability
hypothesis. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumPolynomialGaussian (p a : ℝ) (x : ℂ) : ℝ :=
  (1 + ‖x‖) ^ p * Real.exp (-a * ‖x‖ ^ 2)

theorem equilibriumPolynomialGaussian_nonneg (p a : ℝ) (x : ℂ) :
    0 ≤ equilibriumPolynomialGaussian p a x :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

/-- The logarithmic polynomial weight is absorbed by half of the Gaussian
exponent with an explicit constant exp(p^2/(2a)). -/
theorem equilibriumPolynomialGaussian_bound {p a : ℝ} (hp : 0 ≤ p) (ha : 0 < a) (x : ℂ) :
    equilibriumPolynomialGaussian p a x ≤
      Real.exp (p ^ 2 / (2 * a)) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  have hYoung : p * ‖x‖ ≤ (a / 2) * ‖x‖ ^ 2 + p ^ 2 / (2 * a) := by
    have h : p * ‖x‖ - (a / 2) * ‖x‖ ^ 2 ≤ p ^ 2 / (2 * a) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
      nlinarith [sq_nonneg (a * ‖x‖ - p)]
    linarith
  have hL := mul_le_mul_of_nonneg_left (equilibriumLogMoment_le_norm x) hp
  have hexp : p * equilibriumLogMoment x - a * ‖x‖ ^ 2 ≤
      p ^ 2 / (2 * a) - (a / 2) * ‖x‖ ^ 2 := by linarith
  calc
    equilibriumPolynomialGaussian p a x = Real.exp (p * equilibriumLogMoment x - a * ‖x‖ ^ 2) := by
      unfold equilibriumPolynomialGaussian equilibriumLogMoment
      rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖x‖), ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (p ^ 2 / (2 * a) - (a / 2) * ‖x‖ ^ 2) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem equilibriumPolynomialGaussian_continuous {p : ℝ} (hp : 0 ≤ p) (a : ℝ) :
    Continuous (equilibriumPolynomialGaussian p a) := by
  unfold equilibriumPolynomialGaussian
  exact ((Real.continuous_rpow_const hp).comp (continuous_const.add continuous_norm)).mul
    ((continuous_const.mul (continuous_norm.pow 2)).rexp)

theorem equilibriumPolynomialGaussian_integrable {p a : ℝ} (hp : 0 ≤ p) (ha : 0 < a) :
    Integrable (equilibriumPolynomialGaussian p a) := by
  apply ((integrable_planar_gaussian (half_pos ha)).const_mul (Real.exp (p ^ 2 / (2 * a)))).mono'
    (equilibriumPolynomialGaussian_continuous hp a).measurable.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumPolynomialGaussian_nonneg p a x)]
    exact equilibriumPolynomialGaussian_bound hp ha x)

/-- An explicit real-exponent integral bound, with actual planar normalization. -/
theorem integral_equilibriumPolynomialGaussian_le {p a : ℝ} (hp : 0 ≤ p) (ha : 0 < a) :
    (∫ x : ℂ, equilibriumPolynomialGaussian p a x) ≤
      Real.exp (p ^ 2 / (2 * a)) * (2 * Real.pi / a) := by
  have hi := (integrable_planar_gaussian (half_pos ha)).const_mul (Real.exp (p ^ 2 / (2 * a)))
  have h := integral_mono (equilibriumPolynomialGaussian_integrable hp ha) hi
    (equilibriumPolynomialGaussian_bound hp ha)
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos ha)] at h
  simp only [Complex.finrank_real_complex] at h
  norm_num at h
  have he : Real.pi / (a / 2) = 2 * Real.pi / a := by field_simp <;> ring
  rwa [he] at h

/-- A pointwise Gaussian-polynomial envelope supplies actual integrability
and an explicit integral bound for an arbitrary measurable nonnegative weight. -/
theorem equilibrium_integrable_and_integral_le_of_polynomial_gaussian {w : ℂ → ℝ}
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {p a B : ℝ}
    (hp : 0 ≤ p) (ha : 0 < a) (hB : 0 ≤ B)
    (hwB : ∀ x, w x ≤ B * equilibriumPolynomialGaussian p a x) :
    Integrable w ∧ (∫ x : ℂ, w x) ≤ B * Real.exp (p ^ 2 / (2 * a)) * (2 * Real.pi / a) := by
  have hmajor := (equilibriumPolynomialGaussian_integrable hp ha).const_mul B
  have hi : Integrable w := hmajor.mono' hwm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
      exact hwB x))
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hwB
  rw [integral_const_mul] at h
  have hbound := mul_le_mul_of_nonneg_left (integral_equilibriumPolynomialGaussian_le hp ha) hB
  exact h.trans (by simpa only [mul_assoc] using hbound)

end RepulsiveCoulomb
