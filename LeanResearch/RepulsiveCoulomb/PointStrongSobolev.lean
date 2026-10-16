import LeanResearch.RepulsiveCoulomb.PointStrongSobolevMeasureForm

/-! Complete normalized strong Sobolev moment bound, conditional on the
explicit uniform weak Poincare input. All constants precede the configuration. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointStrongUpgradeFactor (Q : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (2 * pointSobolevKappa Q)) * (2 * (16 : ℝ) ^ (2 * pointSobolevKappa Q)) *
    (universalSmoothTruncationConstant ^ 2) ^ pointSobolevKappa Q

def pointStrongSobolevConstant (Q P : ℝ) : ℝ := pointStrongUpgradeFactor Q * pointWeakSobolevConstant Q P

theorem pointStrongUpgradeFactor_pos (Q : ℝ) : 0 < pointStrongUpgradeFactor Q := by
  unfold pointStrongUpgradeFactor
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)))
    (Real.rpow_pos_of_pos (sq_pos_of_pos universalSmoothTruncationConstant_pos) _)

theorem pointStrongSobolevConstant_pos (Q : ℝ) {P : ℝ} (hP : 0 < P) :
    0 < pointStrongSobolevConstant Q P :=
  mul_pos (pointStrongUpgradeFactor_pos Q) (pointWeakSobolevConstant_pos Q hP)

theorem ofReal_pointStrongUpgradeFactor (Q : ℝ) :
    ENNReal.ofReal (pointStrongUpgradeFactor Q) =
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      ENNReal.ofReal ((universalSmoothTruncationConstant ^ 2) ^ pointSobolevKappa Q) := by
  unfold pointStrongUpgradeFactor
  have hA : 0 ≤ 2 * (2 : ℝ) ^ (2 * pointSobolevKappa Q) := by positivity
  have hB : 0 ≤ 2 * (16 : ℝ) ^ (2 * pointSobolevKappa Q) := by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hA hB), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem rawPointMeasure_strong_sobolev_of_poincare {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q) ∂rawPointMeasure a y) ≤
      pointStrongSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
        (rawPointMeasure a y).real (ball c R) *
        ((∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) /
          (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 0 ≤ pointSobolevKappa Q := (lt_trans zero_lt_one (pointSobolevKappa_gt_one hQ0)).le
  let I := ∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg _)
  have hg : Continuous (fun x => ‖gradient f x‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hf.continuous_fderiv one_ne_zero).norm.pow 2
  have hi : ENNReal.ofReal I = ∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂rawPointMeasure a y :=
    ofReal_integral_eq_lintegral_ofReal (rawPointMeasure_continuous_ball_integrable ha y hg c _)
      (Eventually.of_forall (fun x => sq_nonneg _))
  have h := rawPointMeasure_strong_sobolev_measure_form ha hQ hP y hPI f hf c hR
  rw [← hi, ENNReal.mul_rpow_of_nonneg _ _ hκ,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg universalSmoothTruncationConstant) hκ,
    ENNReal.ofReal_rpow_of_nonneg hI hκ] at h
  have he :
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * pointSobolevKappa Q))) *
      ENNReal.ofReal (pointWeakSobolevBallFactor Q P a y c R) *
      (ENNReal.ofReal ((universalSmoothTruncationConstant ^ 2) ^ pointSobolevKappa Q) * ENNReal.ofReal (I ^ pointSobolevKappa Q)) =
      ENNReal.ofReal (pointStrongUpgradeFactor Q) *
        (ENNReal.ofReal (pointWeakSobolevBallFactor Q P a y c R) * ENNReal.ofReal (I ^ pointSobolevKappa Q)) := by
    rw [ofReal_pointStrongUpgradeFactor]
    ring
  rw [he, ← ENNReal.ofReal_mul (pointWeakSobolevBallFactor_nonneg Q hP a y c hR.le),
    pointWeakSobolevBallFactor_mul_energy Q P a y c R hI,
    ← ENNReal.ofReal_mul (pointStrongUpgradeFactor_pos Q).le] at h
  have hrhs : pointStrongUpgradeFactor Q * (pointWeakSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
      (rawPointMeasure a y).real (ball c R) * (I / (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q) =
      pointStrongSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
      (rawPointMeasure a y).real (ball c R) * (I / (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q := by
    unfold pointStrongSobolevConstant
    ring
  rw [hrhs] at h
  have hp : IntegrableOn (fun x => ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q)) (ball c R) (rawPointMeasure a y) :=
    rawPointMeasure_continuous_ball_integrable ha y
      ((Real.continuous_rpow_const (show 0 ≤ 2 * pointSobolevKappa Q by linarith)).comp
        (hf.continuous.sub continuous_const).norm) c R
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))] at h
  have hn : 0 ≤ pointStrongSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
      (rawPointMeasure a y).real (ball c R) * (I / (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q :=
    mul_nonneg (mul_nonneg (mul_nonneg (pointStrongSobolevConstant_pos Q hP).le
      (Real.rpow_nonneg hR.le _)) ENNReal.toReal_nonneg)
      (Real.rpow_nonneg (div_nonneg hI ENNReal.toReal_nonneg) _)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ENNReal.toReal_ofReal hn] using ht

end RepulsiveCoulomb
