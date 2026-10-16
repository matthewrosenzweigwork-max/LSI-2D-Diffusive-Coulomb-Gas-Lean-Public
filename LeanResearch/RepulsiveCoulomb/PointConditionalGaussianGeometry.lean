module

public import LeanResearch.RepulsiveCoulomb.PointGaussianLocalPoincare

@[expose] public section

/-! Manuscript cor:local-gauss and its integrated local Poincare consequence,
conditional on the one explicit David--Semmes input. Normalization, change of
means and Gaussian comparison are proved, not additional hypotheses. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointGaussian_local_geometry_of_DavidSemmes
    {m : ℕ} {γ Q C : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hC : 0 < C) (y : Fin m → ℂ)
    (hDS : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y v c r ≤
        C * ((rawPointMeasure a y).real (ball c (2 * r)) /
          Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r))) *
        ⨍ z in ball c (2 * r), ‖gradient v z‖ ∂rawPointMeasure a y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    let P := pointMeanTransferConstant Q (C * rawPointDoublingConstant Q * Real.sqrt Real.pi)
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) ^ (1 / (2 * pointSobolevKappa Q)) ≤
      pointGaussianLocalConstant γ Q P * Real.exp (pointGaussianLocalConstant γ Q P * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) ∧
    (∫ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ 2 ∂pointMeasure γ a y) ≤
      (pointGaussianSobolevFactor Q P * Real.exp (61 * γ * R ^ 2) * R ^ 2) *
        ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y := by
  have hK : 0 < C * rawPointDoublingConstant Q * Real.sqrt Real.pi :=
    mul_pos (mul_pos hC (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos)
  have hP := pointMeanTransferConstant_pos Q hK
  have hPI (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (z : ℂ) (r : ℝ) (hr : 0 < r) :=
    rawPoint_physical_weak_one_two_of_DavidSemmes ha hQ hC y v hv (hDS v hv) z hr
  exact ⟨pointMeasure_gaussian_local_sobolev_of_poincare hγ ha hQ hP y hPI f hf hR,
    pointMeasure_gaussian_local_poincare hγ ha hQ hP y hPI f hf (lt_of_lt_of_le zero_lt_one hR)⟩

end RepulsiveCoulomb
