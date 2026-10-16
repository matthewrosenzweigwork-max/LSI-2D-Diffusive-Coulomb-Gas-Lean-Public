import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussianPositivity
import Mathlib.MeasureTheory.Integral.Prod

/-! Gaussian repulsivity for actual integrable signed densities against any
sigma-finite planar reference measure. All triple-integral side conditions
are discharged before Fubini. This will feed the logarithmic Frullani limit. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

private theorem equilibriumGaussianKernel_le_one {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    Real.exp (-s * ‖x - y‖ ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg _))

/-- The signed Gaussian energy is absolutely integrable. -/
theorem equilibriumSignedGaussian_integrable {μ : Measure ℂ} [SFinite μ]
    {s : ℝ} (hs : 0 < s) {f : ℂ → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    Integrable (fun p : ℂ × ℂ => f p.1 * f p.2 * Real.exp (-s * ‖p.1 - p.2‖ ^ 2))
      (μ.prod μ) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by fun_prop)
  exact Eventually.of_forall (fun p => by
    rw [norm_mul, norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (equilibriumGaussianKernel_le_one hs _ _))

/-- Actual overlap representation of the signed Gaussian quadratic energy. -/
theorem equilibriumSignedGaussian_square_identity {μ : Measure ℂ} [SFinite μ]
    {s : ℝ} (hs : 0 < s) {f : ℂ → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    (Real.pi / (4 * s)) *
      (∫ p : ℂ × ℂ, f p.1 * f p.2 * Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂μ.prod μ) =
        ∫ z : ℂ, (∫ x : ℂ, f x * equilibriumGaussianFeature s x z ∂μ) ^ 2 := by
  let G : (ℂ × ℂ) × ℂ → ℝ := fun q =>
    (f q.1.1 * f q.1.2) *
      (equilibriumGaussianFeature s q.1.1 q.2 * equilibriumGaussianFeature s q.1.2 q.2)
  have hGm : Measurable G := by
    dsimp [G, equilibriumGaussianFeature]
    fun_prop
  have hGs (p : ℂ × ℂ) : Integrable (fun z : ℂ => G (p, z)) :=
    (equilibriumGaussianFeature_mul_integrable hs p.1 p.2).const_mul (f p.1 * f p.2)
  have hGn (p : ℂ × ℂ) : (∫ z : ℂ, ‖G (p, z)‖) =
      (‖f p.1‖ * ‖f p.2‖) * (Real.pi / (4 * s)) *
        Real.exp (-s * ‖p.1 - p.2‖ ^ 2) := by
    have he : (fun z : ℂ => ‖G (p, z)‖) = (fun z : ℂ =>
        (‖f p.1‖ * ‖f p.2‖) *
          (equilibriumGaussianFeature s p.1 z * equilibriumGaussianFeature s p.2 z)) := by
      funext z
      dsimp only [G]
      have hpos : 0 < equilibriumGaussianFeature s p.1 z *
          equilibriumGaussianFeature s p.2 z := by
        unfold equilibriumGaussianFeature
        positivity
      rw [norm_mul, norm_mul,
        Real.norm_eq_abs (equilibriumGaussianFeature s p.1 z * equilibriumGaussianFeature s p.2 z),
        abs_of_pos hpos]
    rw [he, integral_const_mul, integral_equilibriumGaussianFeature_mul hs]
    ring
  have hnorm : Integrable (fun p : ℂ × ℂ => ∫ z : ℂ, ‖G (p, z)‖) (μ.prod μ) := by
    have hmajor := (hf.norm.mul_prod hf.norm).const_mul (Real.pi / (4 * s))
    apply hmajor.mono' hGm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _)), hGn]
      have hc : 0 ≤ (‖f p.1‖ * ‖f p.2‖) * (Real.pi / (4 * s)) := by positivity
      have hle := mul_le_mul_of_nonneg_left (equilibriumGaussianKernel_le_one hs p.1 p.2) hc
      simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hle)
  have hG : Integrable G ((μ.prod μ).prod volume) :=
    (integrable_prod_iff hGm.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall hGs, hnorm⟩
  have hswap := integral_integral_swap (μ := μ.prod μ) (ν := volume)
    (f := fun (p : ℂ × ℂ) (z : ℂ) => G (p, z)) hG
  have hleft : (∫ p : ℂ × ℂ, (∫ z : ℂ, G (p, z)) ∂μ.prod μ) =
      (Real.pi / (4 * s)) *
        (∫ p : ℂ × ℂ, f p.1 * f p.2 * Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂μ.prod μ) := by
    calc
      _ = ∫ p : ℂ × ℂ, (Real.pi / (4 * s)) *
          (f p.1 * f p.2 * Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by
          dsimp only [G]
          rw [integral_const_mul, integral_equilibriumGaussianFeature_mul hs]
          ring)
      _ = _ := integral_const_mul _ _
  have hright : (∫ z : ℂ, ∫ p : ℂ × ℂ, G (p, z) ∂μ.prod μ) =
      ∫ z : ℂ, (∫ x : ℂ, f x * equilibriumGaussianFeature s x z ∂μ) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      have he : (fun p : ℂ × ℂ => G (p, z)) =
          (fun p : ℂ × ℂ => (f p.1 * equilibriumGaussianFeature s p.1 z) *
            (f p.2 * equilibriumGaussianFeature s p.2 z)) := by
        funext p
        dsimp only [G]
        ring
      dsimp only
      rw [he, integral_prod_mul
        (fun x : ℂ => f x * equilibriumGaussianFeature s x z)
        (fun x : ℂ => f x * equilibriumGaussianFeature s x z), pow_two])
  rw [hleft, hright] at hswap
  exact hswap

/-- Genuine Gaussian repulsivity for every L1 signed density. -/
theorem equilibriumSignedGaussian_nonneg {μ : Measure ℂ} [SFinite μ]
    {s : ℝ} (hs : 0 < s) {f : ℂ → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    0 ≤ ∫ p : ℂ × ℂ, f p.1 * f p.2 * Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂μ.prod μ := by
  have hn : 0 ≤ ∫ z : ℂ, (∫ x : ℂ, f x * equilibriumGaussianFeature s x z ∂μ) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  rw [← equilibriumSignedGaussian_square_identity hs hfm hf] at hn
  exact nonneg_of_mul_nonneg_right hn (div_pos Real.pi_pos (by positivity))

end RepulsiveCoulomb
