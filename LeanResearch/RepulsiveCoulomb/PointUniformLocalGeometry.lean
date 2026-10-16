import LeanResearch.RepulsiveCoulomb.PointDavidSemmes
import LeanResearch.RepulsiveCoulomb.PointConditionalLocalGeometry
import LeanResearch.RepulsiveCoulomb.PointConditionalGaussianGeometry

/-! Unconditional configuration-uniform local physical Sobolev and Poincare
geometry. The formerly conditional David--Semmes input is discharged by its
actual proved C1 theorem, with no separation or auxiliary analytic hypothesis. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def pointUniformMeanTransferConstant (Q : ℝ) : ℝ :=
  pointMeanTransferConstant Q (pointDavidSemmesConstant Q * rawPointDoublingConstant Q * Real.sqrt Real.pi)

theorem pointUniformMeanTransferConstant_pos (Q : ℝ) : 0 < pointUniformMeanTransferConstant Q :=
  pointMeanTransferConstant_pos Q (mul_pos
    (mul_pos (pointDavidSemmesConstant_pos Q) (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos))

def pointUniformLocalSobolevConstant (Q : ℝ) : ℝ :=
  pointLocalSobolevConstant Q (pointUniformMeanTransferConstant Q)

theorem pointUniformLocalSobolevConstant_pos (Q : ℝ) : 0 < pointUniformLocalSobolevConstant Q :=
  pointLocalSobolevConstant_pos Q (pointUniformMeanTransferConstant_pos Q)

theorem rawPoint_uniform_local_sobolev_poincare {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q) ∂rawPointMeasure a y) ^ (1 / pointSobolevKappa Q) ≤
      pointUniformLocalSobolevConstant Q * R^2 *
        (⨍ x in ball c (11*R), ‖gradient f x‖^2 ∂rawPointMeasure a y) ∧
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖^2 ∂rawPointMeasure a y) ≤
      pointUniformLocalSobolevConstant Q * R^2 *
        (⨍ x in ball c (11*R), ‖gradient f x‖^2 ∂rawPointMeasure a y) :=
  rawPoint_physical_local_sobolev_poincare_of_DavidSemmes ha hQ (pointDavidSemmesConstant_pos Q) y
    (fun v hv x r hr => rawPoint_DavidSemmes_estimate ha hQ y v hv x hr) f hf c hR

theorem pointGaussian_uniform_local_geometry {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) ^ (1 / (2 * pointSobolevKappa Q)) ≤
      pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) *
        Real.exp (pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) * R^2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11*R), ‖gradient f x‖^2 ∂pointMeasure γ a y) ∧
    (∫ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖^2 ∂pointMeasure γ a y) ≤
      (pointGaussianSobolevFactor Q (pointUniformMeanTransferConstant Q) * Real.exp (61*γ*R^2) * R^2) *
        ∫ x in ball (0 : ℂ) (11*R), ‖gradient f x‖^2 ∂pointMeasure γ a y :=
  pointGaussian_local_geometry_of_DavidSemmes hγ ha hQ (pointDavidSemmesConstant_pos Q) y
    (fun v hv x r hr => rawPoint_DavidSemmes_estimate ha hQ y v hv x hr) f hf hR

end RepulsiveCoulomb
