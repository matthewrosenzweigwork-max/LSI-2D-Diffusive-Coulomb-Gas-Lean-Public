import LeanResearch.RepulsiveCoulomb.PointGaussianStrongSobolev

/-! The literal Gaussian local Sobolev corollary, in the manuscript's norm
form, with a single constant in front and in the exponential. The raw weak
Poincare input is still explicit and awaits the David--Semmes proof. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem gaussian_sobolev_sqrt {A F b R E κ : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F) (hR : 0 ≤ R)
    (h : A ^ (1 / κ) ≤ F * Real.exp b * R ^ 2 * E) :
    A ^ (1 / (2 * κ)) ≤ Real.sqrt F * Real.exp (b / 2) * R * Real.sqrt E := by
  have ht := Real.sqrt_le_sqrt h
  have heA : Real.sqrt (A ^ (1 / κ)) = A ^ (1 / (2 * κ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
    congr 1
    ring
  have heE : Real.sqrt (Real.exp b) = Real.exp (b / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hF (Real.exp_pos _).le) (sq_nonneg R)) E,
    Real.sqrt_mul (mul_nonneg hF (Real.exp_pos _).le) (R ^ 2), Real.sqrt_mul hF (Real.exp b),
    Real.sqrt_sq hR, heA, heE] at ht
  exact ht

def pointGaussianLocalConstant (γ Q P : ℝ) : ℝ :=
  1 + Real.sqrt (pointGaussianSobolevFactor Q P) + 61 * γ

theorem pointGaussianLocalConstant_pos {γ : ℝ} (hγ : 0 < γ) (Q P : ℝ) :
    0 < pointGaussianLocalConstant γ Q P := by
  unfold pointGaussianLocalConstant
  have := Real.sqrt_nonneg (pointGaussianSobolevFactor Q P)
  linarith

theorem pointMeasure_gaussian_local_sobolev_of_poincare
    {m : ℕ} {γ Q P : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) ^ (1 / (2 * pointSobolevKappa Q)) ≤
      pointGaussianLocalConstant γ Q P * Real.exp (pointGaussianLocalConstant γ Q P * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs := pointMeasure_gaussian_strong_sobolev_squared_norm hγ ha hQ hP y hPI f hf hR0
  have h := gaussian_sobolev_sqrt (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (pointGaussianSobolevFactor_pos Q hP).le hR0.le hs
  have hC := pointGaussianLocalConstant_pos hγ Q P
  have hcf : Real.sqrt (pointGaussianSobolevFactor Q P) ≤ pointGaussianLocalConstant γ Q P := by
    unfold pointGaussianLocalConstant
    linarith
  have hce : 61 * γ / 2 ≤ pointGaussianLocalConstant γ Q P := by
    unfold pointGaussianLocalConstant
    have := Real.sqrt_nonneg (pointGaussianSobolevFactor Q P)
    linarith
  have he : Real.exp (61 * γ * R ^ 2 / 2) ≤ Real.exp (pointGaussianLocalConstant γ Q P * R ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hce (sq_nonneg R)])
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hcf he (Real.exp_pos _).le hC.le) hR0.le)
    (Real.sqrt_nonneg _))

end RepulsiveCoulomb
