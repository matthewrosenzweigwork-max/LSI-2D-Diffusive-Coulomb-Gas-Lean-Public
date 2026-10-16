import LeanResearch.RepulsiveCoulomb.CoulombGaussianMehler
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Gaussian integration by parts for bounded C¹ functions. All integrability
conditions are established from the literal Gaussian's finite second moment;
no Gaussian integration-by-parts rule is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombGaussian_norm_sq_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : ℂ => ‖z‖ ^ 2) (coulombCenterGaussian β) := by
  rw [coulombCenterGaussian_integrable_iff hβ]
  simpa only [coulombGaussianDensity_eq_equilibrium] using
    equilibriumGaussian_secondMoment_integrable (show 0 < β / 2 by positivity)

theorem coulombGaussian_norm_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : ℂ => ‖z‖) (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  apply ((integrable_const (1 : ℝ)).add (coulombGaussian_norm_sq_integrable hβ)).mono'
    (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖z‖ - 1)]

/-- Explicit linear-growth domination against the Gaussian measure. -/
theorem coulombGaussian_linear_growth_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {A B : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ A + B * ‖z‖) :
    Integrable f (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  exact ((integrable_const A).add ((coulombGaussian_norm_integrable hβ).const_mul B)).mono'
    hf.aestronglyMeasurable (Eventually.of_forall hbound)

theorem coulombGaussianDensity_hasFDerivAt (β : ℝ) (z : ℂ) :
    HasFDerivAt (coulombGaussianDensity β)
      ((-β * coulombGaussianDensity β z) • innerSL ℝ z) z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-β / 2)).exp.const_mul
    (β / (2 * Real.pi))
  have he : (fun y : ℂ => (β / (2 * Real.pi)) * Real.exp ((-β / 2) * ‖y‖ ^ 2)) =
      coulombGaussianDensity β := by
    funext y
    unfold coulombGaussianDensity
    congr 1
    congr 1
    ring
  rw [he] at h
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, coulombGaussianDensity]
  rw [show (-β / 2) * ‖z‖ ^ 2 = -β * ‖z‖ ^ 2 / 2 by ring]
  ring

theorem coulombGaussianDensity_fderiv (β : ℝ) (z v : ℂ) :
    fderiv ℝ (coulombGaussianDensity β) z v =
      -β * coulombGaussianDensity β z * ⟪z, v⟫_ℝ := by
  rw [(coulombGaussianDensity_hasFDerivAt β z).fderiv]
  simp

/-- The Gaussian score pairing of a bounded continuous function is integrable. -/
theorem coulombGaussian_score_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (v : ℂ) :
    Integrable (fun z => ⟪z, v⟫_ℝ * f z) (coulombCenterGaussian β) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  apply coulombGaussian_linear_growth_integrable hβ (by fun_prop)
    (A := 0) (B := ‖v‖ * M)
  intro z
  calc
    ‖⟪z, v⟫_ℝ * f z‖ = |⟪z, v⟫_ℝ| * ‖f z‖ := by rw [norm_mul, Real.norm_eq_abs]
    _ ≤ (‖z‖ * ‖v‖) * M :=
      mul_le_mul (abs_real_inner_le_norm z v) (hM z) (norm_nonneg _) (by positivity)
    _ = 0 + (‖v‖ * M) * ‖z‖ := by ring

/-- Directional derivatives of bounded-C¹ data are genuinely integrable. -/
theorem coulombGaussian_directional_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {D : ℝ}
    (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (v : ℂ) :
    Integrable (fun z => fderiv ℝ f z v) (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  have hc := hf.continuous_fderiv (by norm_num)
  apply (integrable_const (D * ‖v‖)).mono' (by fun_prop)
  filter_upwards [] with z
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hD z) (norm_nonneg v))

/-- The exact physical Gaussian IBP formula, obtained by applying Haar IBP
to the actual density. No support or boundary term is assumed. -/
theorem coulombGaussian_integrationByParts {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (v : ℂ) :
    (∫ z, fderiv ℝ f z v ∂coulombCenterGaussian β) =
      β * ∫ z, ⟪z, v⟫_ℝ * f z ∂coulombCenterGaussian β := by
  have hscore := coulombGaussian_score_integrable hβ hf.continuous hM v
  have hderiv := coulombGaussian_directional_integrable hβ hf hD v
  have hfi := coulombGaussianAverage_integrable hβ hf.continuous hM 0 1 0
  simp only [zero_smul, one_smul, zero_add] at hfi
  have hscore' := (coulombCenterGaussian_integrable_iff hβ _).mp hscore
  have hderiv' := (coulombCenterGaussian_integrable_iff hβ _).mp hderiv
  have hfi' := (coulombCenterGaussian_integrable_iff hβ _).mp hfi
  have hi1 : Integrable (fun z =>
      fderiv ℝ (coulombGaussianDensity β) z v * f z) := by
    apply (hscore'.const_mul (-β)).congr
    filter_upwards [] with z
    rw [coulombGaussianDensity_fderiv]
    ring
  have hi2 : Integrable (fun z => coulombGaussianDensity β z * fderiv ℝ f z v) := by
    simpa only [mul_comm] using hderiv'
  have hi0 : Integrable (fun z => coulombGaussianDensity β z * f z) := by
    simpa only [mul_comm] using hfi'
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := coulombGaussianDensity β) (g := f) (v := v)
    hi1 hi2 hi0
    (fun z _ => (coulombGaussianDensity_hasFDerivAt β z).differentiableAt)
    (fun z _ => hf.differentiable (by norm_num) z)
  rw [integral_coulombCenterGaussian hβ, integral_coulombCenterGaussian hβ]
  rw [hibp]
  have he : (fun z => fderiv ℝ (coulombGaussianDensity β) z v * f z) =
      (fun z => -β * (coulombGaussianDensity β z * (⟪z, v⟫_ℝ * f z))) := by
    funext z
    rw [coulombGaussianDensity_fderiv]
    ring
  rw [he, integral_const_mul]
  ring

end RepulsiveCoulomb
