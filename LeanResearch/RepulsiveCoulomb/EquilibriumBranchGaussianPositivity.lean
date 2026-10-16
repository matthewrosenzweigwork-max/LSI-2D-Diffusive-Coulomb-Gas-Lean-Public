module

public import LeanResearch.RepulsiveCoulomb.WeightedPointNormalization
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! Genuine Gaussian-kernel positivity from its planar overlap representation.
This is the positive-kernel input for the Frullani construction of repulsive
logarithmic energy. Neither Coulomb positivity nor a partition estimate is
assumed. -/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumGaussianFeature (s : ℝ) (x z : ℂ) : ℝ :=
  Real.exp (-(2 * s) * ‖z - x‖ ^ 2)

private theorem equilibrium_gaussian_parallelogram (x y z : ℂ) :
    2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 =
      4 * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2 + ‖x - y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem equilibriumGaussianFeature_mul (s : ℝ) (x y z : ℂ) :
    equilibriumGaussianFeature s x z * equilibriumGaussianFeature s y z =
      Real.exp (-s * ‖x - y‖ ^ 2) *
        Real.exp (-(4 * s) * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2) := by
  unfold equilibriumGaussianFeature
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have h := congrArg (fun t : ℝ => s * t) (equilibrium_gaussian_parallelogram x y z)
  nlinarith

theorem equilibriumGaussianFeature_mul_integrable {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    Integrable (fun z : ℂ => equilibriumGaussianFeature s x z *
      equilibriumGaussianFeature s y z) := by
  have h := ((integrable_planar_gaussian (show 0 < 4 * s by positivity)).comp_sub_right
    ((1 / 2 : ℝ) • (x + y))).const_mul (Real.exp (-s * ‖x - y‖ ^ 2))
  simpa only [equilibriumGaussianFeature_mul] using h

/-- Exact Gaussian overlap formula with the physical planar volume. -/
theorem integral_equilibriumGaussianFeature_mul {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    (∫ z : ℂ, equilibriumGaussianFeature s x z * equilibriumGaussianFeature s y z) =
      (Real.pi / (4 * s)) * Real.exp (-s * ‖x - y‖ ^ 2) := by
  simp_rw [equilibriumGaussianFeature_mul]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun z : ℂ => Real.exp (-(4 * s) * ‖z‖ ^ 2)) ((1 / 2 : ℝ) • (x + y)),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (show 0 < 4 * s by positivity)]
  simp only [Complex.finrank_real_complex]
  norm_num
  ring

/-- An actual finite signed Gaussian quadratic form is nonnegative, with
no restriction on the points, coefficients, or number of points. -/
theorem equilibriumGaussianKernel_positive {ι : Type*} [Fintype ι]
    {s : ℝ} (hs : 0 < s) (a : ι → ℝ) (x : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, a i * a j * Real.exp (-s * ‖x i - x j‖ ^ 2) := by
  classical
  have hij (i j : ι) : Integrable (fun z : ℂ =>
      (a i * equilibriumGaussianFeature s (x i) z) *
        (a j * equilibriumGaussianFeature s (x j) z)) := by
    have h := (equilibriumGaussianFeature_mul_integrable hs (x i) (x j)).const_mul (a i * a j)
    convert h using 1
    funext z
    ring
  have he (z : ℂ) : (∑ i, a i * equilibriumGaussianFeature s (x i) z) ^ 2 =
      ∑ i, ∑ j, (a i * equilibriumGaussianFeature s (x i) z) *
        (a j * equilibriumGaussianFeature s (x j) z) := by
    rw [pow_two, Fintype.sum_mul_sum]
  have hnonneg : 0 ≤ ∫ z : ℂ, (∑ i, a i * equilibriumGaussianFeature s (x i) z) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hi : (∫ z : ℂ, (∑ i, a i * equilibriumGaussianFeature s (x i) z) ^ 2) =
      (Real.pi / (4 * s)) *
        (∑ i, ∑ j, a i * a j * Real.exp (-s * ‖x i - x j‖ ^ 2)) := by
    simp_rw [he]
    rw [integral_finsetSum]
    · simp_rw [integral_finsetSum _ (fun j _ => hij _ j)]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hfun : (fun z : ℂ => (a i * equilibriumGaussianFeature s (x i) z) *
          (a j * equilibriumGaussianFeature s (x j) z)) =
          (fun z : ℂ => (a i * a j) *
            (equilibriumGaussianFeature s (x i) z * equilibriumGaussianFeature s (x j) z)) := by
        funext z
        ring
      rw [hfun, integral_const_mul, integral_equilibriumGaussianFeature_mul hs]
      ring
    · intro i _
      exact integrable_finset_sum _ (fun j _ => hij i j)
  rw [hi] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg (div_pos Real.pi_pos (by positivity))

end RepulsiveCoulomb
