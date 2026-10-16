import LeanResearch.RepulsiveCoulomb.PointWeightedPolygonalChain
import LeanResearch.RepulsiveCoulomb.PointWeightedCrossingArea

/-! A configuration-uniform crossing-area bound for the actual finite weighted
chain. The constants depend only on the total exponent budget. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def pointWeightedChainCrossingConstant (Q : ℝ) : ℝ :=
  rawPointGrowthConstant (2 * Q) * (6 : ℝ) ^ (2 * Q + 2) * (Real.pi * Real.exp (8 * Q))

theorem pointWeightedChainCrossingConstant_pos (Q : ℝ) :
    0 < pointWeightedChainCrossingConstant Q := by
  unfold pointWeightedChainCrossingConstant
  exact mul_pos (mul_pos (rawPointGrowthConstant_pos _) (Real.rpow_pos_of_pos (by norm_num) _)) (by positivity)

theorem pointSquaredBallArea_le_crossingChainLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) (p : ℕ → ℂ) (n : ℕ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hstart : dist (p 0) c ≤ 5 * R / 4) (hsep : R / 2 ≤ dist (p n) (p 0)) :
    (rawPointMeasure (fun j => 2 * a j) y).real (ball c R) ≤
      pointWeightedChainCrossingConstant Q * rawPointChainLength a y p n ^ 2 := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hQ2 : ∑ j, 2 * a j ≤ 2 * Q := by rw [← Finset.mul_sum]; linarith
  have hsub : closedBall c R ⊆ closedBall (p 0) (3 * R) := by
    intro z hz
    have hh := dist_triangle z c (p 0)
    have hz' : dist z c ≤ R := hz
    have hc : dist c (p 0) ≤ 5 * R / 4 := by simpa only [dist_comm] using hstart
    exact mem_closedBall.mpr (by linarith)
  have hm := setIntegral_mono_set (rawPointWeight_ball_integrable ha2 y (p 0) (3 * R))
    (Filter.Eventually.of_forall (rawPointWeight_nonneg (fun j => 2 * a j) y))
    (Filter.Eventually.of_forall hsub)
  have hg := rawPointWeight_volume_growth ha2 hQ2 y (p 0) (by linarith : 0 < R / 2)
    (by norm_num : (1 : ℝ) ≤ 6)
  have hrad : 6 * (R / 2) = 3 * R := by ring
  rw [hrad] at hg
  have hdR : R / 2 ≤ ‖p n - p 0‖ := by simpa only [dist_eq_norm] using hsep
  have hn := setIntegral_mono_set (rawPointWeight_ball_integrable ha2 y (p 0) ‖p n - p 0‖)
    (Filter.Eventually.of_forall (rawPointWeight_nonneg (fun j => 2 * a j) y))
    (Filter.Eventually.of_forall (closedBall_subset_closedBall hdR))
  have hb := ballIntegral_le_pointConformalEDist_sq ha2 hQ2 y (p 0) (p n)
  have he : 4 * (2 * Q) = 8 * Q := by ring
  rw [he] at hb
  have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (pointDoubleEDist_le_chainLength ha y p n)
  rw [ENNReal.toReal_ofReal (rawPointChainLength_nonneg a y p n)] at hd
  have hnn := ENNReal.toReal_nonneg (a := pointSmoothConformalEDist (fun j => 2 * a j) y (p 0) (p n))
  have hs : (pointSmoothConformalEDist (fun j => 2 * a j) y (p 0) (p n)).toReal ^ 2 ≤
      rawPointChainLength a y p n ^ 2 := by nlinarith
  have hc : 0 ≤ rawPointGrowthConstant (2 * Q) * (6 : ℝ) ^ (2 * Q + 2) :=
    mul_nonneg (rawPointGrowthConstant_pos _).le (Real.rpow_nonneg (by norm_num) _)
  rw [rawPointMeasure_ball_real_eq_integral ha2]
  calc
    _ ≤ _ := hm
    _ ≤ _ := hg
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))) hc
    _ = _ := by unfold pointWeightedChainCrossingConstant; ring

end RepulsiveCoulomb
