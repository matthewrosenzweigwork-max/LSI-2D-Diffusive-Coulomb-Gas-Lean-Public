import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianLocalGeometry
import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolev

/-! Additive experimental source. Verification status is recorded separately in evidence. The actual new generic doubling/weak-PI
producer supplies the raw Sobolev input used by the Gaussian transfer.
The exponent is determined by the supplied doubling constant, independently
of any total point-weight parameter. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem gaussian_local_geometry_of_doubling
    {m : ℕ} {γ D P : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hD : GlobalDoublingWith (rawPointMeasure a y) D)
    (hμ : PositiveFiniteBalls (rawPointMeasure a y)) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖
        ∂rawPointMeasure a y) ≤
      P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2
        ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
        (2 * doublingSobolevKappa D) ∂pointMeasure γ a y) ^
          (1 / (2 * doublingSobolevKappa D)) ≤
      gaussianLocalConstant γ (doublingSobolevKappa D) (doublingLocalSobolevConstant D P) *
        Real.exp (gaussianLocalConstant γ (doublingSobolevKappa D)
          (doublingLocalSobolevConstant D P) * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) ∧
    (∫ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ 2 ∂pointMeasure γ a y) ≤
      (gaussianSobolevFactor (doublingSobolevKappa D) (doublingLocalSobolevConstant D P) *
        Real.exp (61 * γ * R ^ 2) * R ^ 2) *
      ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y := by
  have hκ := doublingSobolevKappa_gt_one D
  have hS := doublingLocalSobolevConstant_pos hD.1 hP
  have hraw := fun (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (r : ℝ) (hr : 0 < r) =>
    strong_sobolev_squared_norm hD hμ hP hPI v hv (0 : ℂ) hr
  exact ⟨gaussian_local_sobolev hγ ha hκ hS y hraw f hf hR,
    gaussian_local_poincare hγ ha hκ hS y hraw f hf (lt_of_lt_of_le zero_lt_one hR)⟩

end RepulsiveCoulomb.PaperRoute
