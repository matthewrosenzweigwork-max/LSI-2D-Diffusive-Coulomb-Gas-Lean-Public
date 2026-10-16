module

public import LeanResearch.RepulsiveCoulomb.CoulombGaussianEntropyDerivative
public import LeanResearch.RepulsiveCoulomb.CoulombGaussianInterpolationEndpoints

@[expose] public section

/-! Sharp logarithmic Sobolev inequality for the actual planar center
Gaussian β/(2π) exp(-β|z|²/2). The analytic chain is concrete: literal Mehler
kernel, Gaussian rotation, Gaussian integration by parts, entropy derivative,
weighted Cauchy--Schwarz, compact interpolation, and positive regularization.
Sharpness uses compact smooth radial cutoffs of a genuine exponential witness.
No entropy, semigroup, tensorization, or sharpness assumption is retained. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Exact positive-function Gaussian entropy--Fisher inequality, obtained from
the actual differentiated entropy integral rather than an assumed flow. -/
theorem coulombCenterGaussian_positive_fisher {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {M D m : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hm : 0 < m) (hgm : ∀ z, m ≤ g z) :
    entropy (coulombCenterGaussian β) g ≤
      (((1 / (2 * β)) * ∫ x, coulombGaussianFisherDensity g x ∂coulombCenterGaussian β : ℝ) : EReal) :=
  coulombGaussian_positive_fisher_of_interpolation_derivative hβ hg hM hD hm hgm
    (fun s hs => coulombGaussianInterpolationEntropy_hasDerivAt hβ hg hM hD hm hgm hs.1 hs.2)

/-- The exact Gaussian LSI on the original compact smooth planar test class,
with the standard real physical gradient and the sharp coefficient 2/β. -/
theorem coulombCenterGaussian_core_lsi {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
      (((2 / β) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal) := by
  apply coulombGaussian_core_lsi_of_positive_fisher hβ
  intro g hg M D m hM hD hm hgm
  exact coulombCenterGaussian_positive_fisher hβ hg hM hD hm hgm

/-- Exact characterization of every positive admissible rate, including the
sharp endpoint and excluding every larger rate by compact smooth witnesses. -/
theorem coulombCenterGaussian_core_lsi_iff {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) :
    (∀ φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤,
      entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
        (((2 / ρ) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal)) ↔
      ρ ≤ β := by
  constructor
  · exact coulombCenterGaussian_core_lsi_rate_le hβ hρ
  · intro hρβ φ
    have hcoeff : 2 / β ≤ 2 / ρ :=
      div_le_div_of_nonneg_left (by norm_num) hρ hρβ
    have hE : 0 ≤ ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β :=
      integral_nonneg (fun z => sq_nonneg _)
    exact (coulombCenterGaussian_core_lsi hβ φ).trans
      (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hcoeff hE))

end RepulsiveCoulomb
