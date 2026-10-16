module

public import LeanResearch.RepulsiveCoulomb.PointGaussianAverageComparison
public import LeanResearch.RepulsiveCoulomb.AverageRpowCentering

@[expose] public section

/-! The actual change of weighted mean in Gaussian local Sobolev transfer. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointMeasure_raw_centered_moment_comparison {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R q : ℝ} (hR : 0 < R) (hq : 1 ≤ q) (f : ℂ → ℝ) (hf : Continuous f) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ q ∂pointMeasure γ a y) ≤
      (2 * (2 : ℝ) ^ q) * Real.exp (γ * R ^ 2 / 2) *
        (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y)‖ ^ q ∂rawPointMeasure a y) := by
  let ν := (pointMeasure γ a y).restrict (ball (0 : ℂ) R)
  let c := ⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y
  letI := pointMeasure_isProbability hγ ha y
  letI : IsFiniteMeasure ν := inferInstance
  letI : NeZero ν := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (pointMeasure_origin_ball_pos hγ ha y hR).ne' (by simpa [ν] using he)⟩
  have hc (b : ℝ) : Continuous (fun x => ‖f x - b‖ ^ q) :=
    (Real.continuous_rpow_const (zero_le_one.trans hq)).comp (hf.sub continuous_const).norm
  have hp (b : ℝ) : Integrable (fun x => ‖f x - b‖ ^ q) ν :=
    pointMeasure_continuous_ball_integrable hγ ha y (hc b) 0 R
  have h := average_rpow_mean_centering ν hf.measurable
    (pointMeasure_continuous_ball_integrable hγ ha y hf 0 R) c hq (hp c) (hp _)
  have ht := (pointMeasure_raw_average_comparison hγ ha y hR
    (fun x => ‖f x - c‖ ^ q) (hc c) (fun x => Real.rpow_nonneg (norm_nonneg _) _)).1
  apply h.trans
  calc
    _ ≤ (2 * (2 : ℝ) ^ q) * (Real.exp (γ * R ^ 2 / 2) *
        (⨍ x in ball (0 : ℂ) R, ‖f x - c‖ ^ q ∂rawPointMeasure a y)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by dsimp only [c]; ring

theorem rpow_compare_factor {A B T D κ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 0 ≤ T) (hD : 1 ≤ D) (hκ : 1 ≤ κ) (h : A ≤ T * D * B) :
    A ^ (1 / κ) ≤ T ^ (1 / κ) * D * B ^ (1 / κ) := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hd : 0 ≤ D := zero_le_one.trans hD
  have hpow := Real.rpow_le_rpow hA h (show 0 ≤ 1 / κ by positivity)
  rw [Real.mul_rpow (mul_nonneg hT hd) hB, Real.mul_rpow hT hd] at hpow
  apply hpow.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hD ((div_le_one hk).mpr hκ))
      (Real.rpow_nonneg hT _)) (Real.rpow_nonneg hB _)

end RepulsiveCoulomb
