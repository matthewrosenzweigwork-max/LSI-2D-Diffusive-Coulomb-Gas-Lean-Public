module

public import LeanResearch.RepulsiveCoulomb.PointStrongSobolevAverage

@[expose] public section

/-! Standard squared-norm form of the complete local Sobolev upgrade, with
literal inner/outer averages and a configuration-independent constant. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem sobolev_moment_root {A C R E κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hκ : 0 < κ)
    (h : A ≤ C * R ^ (2 * κ) * E ^ κ) :
    A ^ (1 / κ) ≤ C ^ (1 / κ) * R ^ 2 * E := by
  have ht := Real.rpow_le_rpow hA h (show 0 ≤ 1 / κ by positivity)
  have he1 : (2 * κ) * (1 / κ) = 2 := by field_simp
  have he2 : κ * (1 / κ) = 1 := by field_simp
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hR _)) (Real.rpow_nonneg hE _),
    Real.mul_rpow hC (Real.rpow_nonneg hR _), ← Real.rpow_mul hR,
    ← Real.rpow_mul hE, he1, he2, Real.rpow_two, Real.rpow_one] at ht
  exact ht

def pointLocalSobolevConstant (Q P : ℝ) : ℝ :=
  (pointStrongSobolevConstant Q P) ^ (1 / pointSobolevKappa Q) *
    (rawPointGrowthConstant Q * (11 : ℝ) ^ (Q + 2))

theorem pointLocalSobolevConstant_pos (Q : ℝ) {P : ℝ} (hP : 0 < P) :
    0 < pointLocalSobolevConstant Q P :=
  mul_pos (Real.rpow_pos_of_pos (pointStrongSobolevConstant_pos Q hP) _)
    (mul_pos (rawPointGrowthConstant_pos Q) (Real.rpow_pos_of_pos (by norm_num) _))

theorem rawPointMeasure_strong_sobolev_squared_norm {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * pointSobolevKappa Q) ∂rawPointMeasure a y) ^ (1 / pointSobolevKappa Q) ≤
      pointLocalSobolevConstant Q P * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 0 < pointSobolevKappa Q := lt_trans zero_lt_one (pointSobolevKappa_gt_one hQ0)
  have h := sobolev_moment_root
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (pointStrongSobolevConstant_pos Q hP).le hR.le
    (div_nonneg (integral_nonneg (fun x => sq_nonneg _)) ENNReal.toReal_nonneg) hκ
    (rawPointMeasure_strong_sobolev_average_moment ha hQ hP y hPI f hf c hR)
  have he := rawPointMeasure_energy_ratio_le_outer_average ha hQ y (fun x => ‖gradient f x‖ ^ 2)
    (fun x => sq_nonneg _) c hR
  apply h.trans
  calc
    _ ≤ (pointStrongSobolevConstant Q P) ^ (1 / pointSobolevKappa Q) * R ^ 2 *
        ((rawPointGrowthConstant Q * (11 : ℝ) ^ (Q + 2)) *
          (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (pointStrongSobolevConstant_pos Q hP).le _) (sq_nonneg R))
    _ = _ := by unfold pointLocalSobolevConstant; ring

end RepulsiveCoulomb
