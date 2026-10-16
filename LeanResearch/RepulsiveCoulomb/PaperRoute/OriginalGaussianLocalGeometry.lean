import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalPointGeometry
import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianFromDoubling

/-! Additive experimental source. Verification status is recorded separately in evidence. The original finite configuration
feeds the actual same-map Bonk--Lang/Semmes/DS producer, then the newly proved
generic doubling Sobolev producer. No old local-geometry constants are chosen.
This module must not be promoted until OriginalPointGeometry is validated. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

def originalGaussianKappa (Q : ℝ) : ℝ :=
  doublingSobolevKappa (originalPointDoublingConstant Q)

def originalRawSobolevConstant (Q : ℝ) : ℝ :=
  doublingLocalSobolevConstant (originalPointDoublingConstant Q)
    (originalPointWeakTwoConstant Q * originalPointDoublingConstant Q)

theorem originalGaussianKappa_gt_one (Q : ℝ) : 1 < originalGaussianKappa Q :=
  doublingSobolevKappa_gt_one _

theorem original_uniform_raw_strong_sobolev (Q : ℝ) :
    UniformRawStrongSobolev Q (originalGaussianKappa Q) (originalRawSobolevConstant Q) := by
  intro m a ha y hQ f hf R hR
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg fun j _ => ha j).trans hQ
  obtain ⟨_, _, _, _, _, _, hP, _⟩ := originalPoint_constants_pos hQ0
  obtain ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩ := original_point_localGeometry ha hQ y
  have hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r,
        ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      originalPointWeakTwoConstant Q * r * Real.sqrt
        (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y) := by
    intro v hv z r hr
    simpa only [Real.norm_eq_abs, PlanarDS.norm_gradient_eq_norm_fderiv] using hPI2 v hv z r hr
  exact strong_sobolev_squared_norm_of_dilation_two hD hμ hP hPI f hf 0 hR

/-- Positivity is obtained from the same actual original-configuration
producer at an empty configuration, so no old point doubling bound is used. -/
theorem originalRawSobolevConstant_pos {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < originalRawSobolevConstant Q := by
  obtain ⟨_, _, _, _, _, _, hP, _⟩ := originalPoint_constants_pos hQ
  obtain ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩ :=
    original_point_localGeometry (m := 0) (a := fun _ => 0) (by intro j; exact Fin.elim0 j)
      (by simpa using hQ) (fun j => Fin.elim0 j)
  exact doublingLocalSobolevConstant_pos hD.1 (mul_pos hP (lt_of_lt_of_le zero_lt_one hD.1))

theorem original_gaussian_local_geometry {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
        (2 * originalGaussianKappa Q) ∂pointMeasure γ a y) ^
          (1 / (2 * originalGaussianKappa Q)) ≤
      gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) *
        Real.exp (gaussianLocalConstant γ (originalGaussianKappa Q)
          (originalRawSobolevConstant Q) * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) ∧
    (∫ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ 2 ∂pointMeasure γ a y) ≤
      (gaussianSobolevFactor (originalGaussianKappa Q) (originalRawSobolevConstant Q) *
        Real.exp (61 * γ * R ^ 2) * R ^ 2) *
      ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg fun j _ => ha j).trans hQ
  have hκ := originalGaussianKappa_gt_one Q
  have hS := originalRawSobolevConstant_pos hQ0
  have hraw := original_uniform_raw_strong_sobolev Q m a ha y hQ
  exact ⟨gaussian_local_sobolev hγ ha hκ hS y hraw f hf hR,
    gaussian_local_poincare hγ ha hκ hS y hraw f hf (lt_of_lt_of_le zero_lt_one hR)⟩

end RepulsiveCoulomb.PaperRoute
