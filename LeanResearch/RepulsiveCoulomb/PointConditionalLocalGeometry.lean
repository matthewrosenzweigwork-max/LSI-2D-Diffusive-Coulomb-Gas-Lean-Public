module

public import LeanResearch.RepulsiveCoulomb.PointStrongLocalPoincare

@[expose] public section

/-! Complete conditional local analytic bridge from the explicitly displayed
David--Semmes input to strong Sobolev and quadratic Poincare, using the actual
raw point measure and physical real Euclidean gradient. David--Semmes remains
an unproved hypothesis; this file is not unconditional local geometry or LSI. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPoint_physical_local_sobolev_poincare_of_DavidSemmes
    {m : ℕ} {Q C : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hC : 0 < C) (y : Fin m → ℂ)
    (hDS : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y v c r ≤
        C * ((rawPointMeasure a y).real (ball c (2 * r)) /
          Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r))) *
        ⨍ z in ball c (2 * r), ‖gradient v z‖ ∂rawPointMeasure a y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    let S := pointLocalSobolevConstant Q
      (pointMeanTransferConstant Q (C * rawPointDoublingConstant Q * Real.sqrt Real.pi))
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q) ∂rawPointMeasure a y) ^ (1 / pointSobolevKappa Q) ≤
      S * R ^ 2 * (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) ∧
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^ 2 ∂rawPointMeasure a y) ≤
      S * R ^ 2 * (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  have hK : 0 < C * rawPointDoublingConstant Q * Real.sqrt Real.pi :=
    mul_pos (mul_pos hC (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos)
  have hP := pointMeanTransferConstant_pos Q hK
  have hPI (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (z : ℂ) (r : ℝ) (hr : 0 < r) :=
    rawPoint_physical_weak_one_two_of_DavidSemmes ha hQ hC y v hv (hDS v hv) z hr
  exact ⟨rawPointMeasure_strong_sobolev_squared_norm ha hQ hP y hPI f hf c hR,
    rawPointMeasure_strong_local_poincare ha hQ hP y hPI f hf c hR⟩

theorem pointConditionalLocalGeometry_constant_pos (Q : ℝ) {C : ℝ} (hC : 0 < C) :
    0 < pointLocalSobolevConstant Q
      (pointMeanTransferConstant Q (C * rawPointDoublingConstant Q * Real.sqrt Real.pi)) :=
  pointLocalSobolevConstant_pos Q (pointMeanTransferConstant_pos Q
    (mul_pos (mul_pos hC (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos)))

end RepulsiveCoulomb
