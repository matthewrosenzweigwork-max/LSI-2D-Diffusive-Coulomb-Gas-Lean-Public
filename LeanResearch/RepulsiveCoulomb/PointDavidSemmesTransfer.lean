module

public import LeanResearch.RepulsiveCoulomb.PointMeanTransfer

@[expose] public section

/-! Connect the exact quoted David--Semmes double-average form to the completed
mean transfer, using the proved raw/squared-weight radius factor. The displayed
David--Semmes estimate remains a hypothesis, not a claimed proved theorem. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace RepulsiveCoulomb

theorem rawPoint_mean_transfer_of_DavidSemmes_estimate {m : ℕ} {Q C : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hC : 0 < C) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hDS : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        C * ((rawPointMeasure a y).real (ball c (2 * r)) /
          Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r))) *
        ⨍ z in ball c (2 * r), g z ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      pointMeanTransferConstant Q (C * rawPointDoublingConstant Q * Real.sqrt Real.pi) * R *
        ⨍ z in ball c (5 * R), g z ∂rawPointMeasure a y := by
  have hK : 0 < C * rawPointDoublingConstant Q * Real.sqrt Real.pi :=
    mul_pos (mul_pos hC (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos)
  apply rawPoint_mean_transfer_of_double_average_bound ha hQ hK y f g hf hg hgn _ c hR
  intro d r hr
  apply (hDS d r hr).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rawPointMeasure_squared_weight_radius_factor ha hQ y d hr) hC.le)
    (average_nonneg (μ := (rawPointMeasure a y).restrict (ball d (2 * r))) hgn)
  convert h using 1
  ring

end RepulsiveCoulomb
