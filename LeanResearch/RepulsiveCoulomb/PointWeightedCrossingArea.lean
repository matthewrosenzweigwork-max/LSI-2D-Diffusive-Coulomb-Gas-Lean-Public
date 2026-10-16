module

public import LeanResearch.RepulsiveCoulomb.PointWeightedBoundaryArea

@[expose] public section

/-! A path crossing the annulus from B(c,R) to outside B(c,2R) has uniformly
positive squared weighted length relative to the squared-weight mass of B(c,R).
This supplies the crossing-component case of a future relative separator proof. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def pointWeightedCrossingConstant (Q : ℝ) : ℝ :=
  rawPointGrowthConstant (2 * Q) * (2 : ℝ) ^ (2 * Q + 2) *
    (Real.pi * Real.exp (8 * Q))

theorem pointWeightedCrossingConstant_pos (Q : ℝ) :
    0 < pointWeightedCrossingConstant Q := by
  unfold pointWeightedCrossingConstant
  exact mul_pos (mul_pos (rawPointGrowthConstant_pos _) (Real.rpow_pos_of_pos (by norm_num) _)) (by positivity)

theorem pointSquaredBallArea_le_crossingLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≤ t) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hs : γ s ∈ closedBall c R) (ht : γ t ∉ ball c (2 * R)) :
    (rawPointMeasure (fun j => 2 * a j) y).real (ball c R) ≤
      pointWeightedCrossingConstant Q * rawPointPathLength a y γ s t ^ 2 := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hQ2 : ∑ j, 2 * a j ≤ 2 * Q := by rw [← Finset.mul_sum]; linarith
  have hs' : dist (γ s) c ≤ R := hs
  have ht' : 2 * R ≤ dist (γ t) c := le_of_not_gt ht
  have hd : R ≤ ‖γ t - γ s‖ := by
    have hh := dist_triangle (γ t) (γ s) c
    rw [dist_eq_norm (γ t) (γ s)] at hh
    linarith
  have hsub : closedBall c R ⊆ closedBall (γ s) (2 * R) := by
    intro z hz
    have hh := dist_triangle z c (γ s)
    have hz' : dist z c ≤ R := hz
    have hc : dist c (γ s) ≤ R := by simpa only [dist_comm] using hs'
    exact mem_closedBall.mpr (by linarith)
  have hm := setIntegral_mono_set (rawPointWeight_ball_integrable ha2 y (γ s) (2 * R))
    (Filter.Eventually.of_forall (rawPointWeight_nonneg (fun j => 2 * a j) y))
    (Filter.Eventually.of_forall hsub)
  have hg := rawPointWeight_volume_growth ha2 hQ2 y (γ s) hR (by norm_num : (1 : ℝ) ≤ 2)
  have hn := setIntegral_mono_set
    (rawPointWeight_ball_integrable ha2 y (γ s) ‖γ t - γ s‖)
    (Filter.Eventually.of_forall (rawPointWeight_nonneg (fun j => 2 * a j) y))
    (Filter.Eventually.of_forall (closedBall_subset_closedBall hd))
  have hb := pointSquaredBallArea_le_rawPointPathLength_sq ha hQ y hγ hst
  rw [rawPointMeasure_ball_real_eq_integral ha2] at hb ⊢
  have hc : 0 ≤ rawPointGrowthConstant (2 * Q) * (2 : ℝ) ^ (2 * Q + 2) := by
    exact mul_nonneg (rawPointGrowthConstant_pos _).le (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ _ := hm
    _ ≤ _ := hg
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hc
    _ = _ := by unfold pointWeightedCrossingConstant; ring

end RepulsiveCoulomb
