module

public import LeanResearch.RepulsiveCoulomb.PointGaussianCenterComparison
public import LeanResearch.RepulsiveCoulomb.PointStrongSobolevRoot

@[expose] public section

/-! Gaussian local Sobolev transfer with explicit exponential-in-radius-square
loss, conditional on the displayed raw weak Poincare input. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointGaussianSobolevFactor (Q P : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (2 * pointSobolevKappa Q)) ^ (1 / pointSobolevKappa Q) * pointLocalSobolevConstant Q P

theorem pointGaussianSobolevFactor_pos (Q : ℝ) {P : ℝ} (hP : 0 < P) :
    0 < pointGaussianSobolevFactor Q P :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) _)
    (pointLocalSobolevConstant_pos Q hP)

theorem pointMeasure_gaussian_strong_sobolev_squared_norm
    {m : ℕ} {γ Q P : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) ^ (1 / pointSobolevKappa Q) ≤
      pointGaussianSobolevFactor Q P * Real.exp (61 * γ * R ^ 2) * R ^ 2 *
        (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 1 ≤ pointSobolevKappa Q := (pointSobolevKappa_gt_one hQ0).le
  have hq : 1 ≤ 2 * pointSobolevKappa Q := by linarith
  let T := 2 * (2 : ℝ) ^ (2 * pointSobolevKappa Q)
  let D := Real.exp (γ * R ^ 2 / 2)
  let S := pointLocalSobolevConstant Q P
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (by nlinarith [sq_nonneg R])
  have hroot := rpow_compare_factor
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hT hD hκ
    (pointMeasure_raw_centered_moment_comparison hγ ha y hR hq f hf.continuous)
  have hs := rawPointMeasure_strong_sobolev_squared_norm ha hQ hP y hPI f hf 0 hR
  have hg : Continuous (fun x => ‖gradient f x‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hf.continuous_fderiv one_ne_zero).norm.pow 2
  have hgrad := (pointMeasure_raw_average_comparison hγ ha y (show 0 < 11 * R by positivity)
    (fun x => ‖gradient f x‖ ^ 2) hg (fun x => sq_nonneg _)).2
  have he : D * Real.exp (γ * (11 * R) ^ 2 / 2) = Real.exp (61 * γ * R ^ 2) := by
    dsimp [D]
    rw [← Real.exp_add]
    congr 1
    ring
  apply hroot.trans
  calc
    _ ≤ T ^ (1 / pointSobolevKappa Q) * D *
        (S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.rpow_nonneg hT _) (Real.exp_pos _).le)
    _ ≤ T ^ (1 / pointSobolevKappa Q) * D *
        (S * R ^ 2 * (Real.exp (γ * (11 * R) ^ 2 / 2) *
          (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrad
        (mul_nonneg (pointLocalSobolevConstant_pos Q hP).le (sq_nonneg R)))
        (mul_nonneg (Real.rpow_nonneg hT _) (Real.exp_pos _).le)
    _ = (T ^ (1 / pointSobolevKappa Q) * S) * (D * Real.exp (γ * (11 * R) ^ 2 / 2)) * R ^ 2 *
        (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by ring
    _ = _ := by rw [he]; rfl

end RepulsiveCoulomb
