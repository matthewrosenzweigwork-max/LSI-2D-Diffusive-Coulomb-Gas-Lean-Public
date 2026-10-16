module

public import LeanResearch.RepulsiveCoulomb.PointGaussianLocalSobolev
public import LeanResearch.RepulsiveCoulomb.PowerMeanComparison

@[expose] public section

/-! Actual Gaussian local quadratic Poincare, in integrated form suitable for
the global quadratic-moment absorption. The raw weak Poincare input remains
explicit; no global coercivity is assumed or asserted. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointMeasure_gaussian_local_poincare
    {m : ℕ} {γ Q P : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ 2 ∂pointMeasure γ a y) ≤
      (pointGaussianSobolevFactor Q P * Real.exp (61 * γ * R ^ 2) * R ^ 2) *
        ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y := by
  let μ := (pointMeasure γ a y).restrict (ball (0 : ℂ) R)
  let u : ℂ → ℝ := fun x => f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)
  let M := (pointMeasure γ a y).real (ball (0 : ℂ) R)
  let N := (pointMeasure γ a y).real (ball (0 : ℂ) (11 * R))
  let I := ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y
  let A := pointGaussianSobolevFactor Q P * Real.exp (61 * γ * R ^ 2) * R ^ 2
  letI := pointMeasure_isProbability hγ ha y
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (pointMeasure_origin_ball_pos hγ ha y hR).ne' (by simpa [μ] using he)⟩
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 1 ≤ pointSobolevKappa Q := (pointSobolevKappa_gt_one hQ0).le
  have hu : Continuous u := hf.continuous.sub continuous_const
  have hs : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    pointMeasure_continuous_ball_integrable hγ ha y (hu.norm.pow 2) 0 R
  have hp : Integrable (fun x => ‖u x‖ ^ (2 * pointSobolevKappa Q)) μ :=
    pointMeasure_continuous_ball_integrable hγ ha y
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * pointSobolevKappa Q)).comp hu.norm) 0 R
  have hvar := (average_sq_le_average_rpow μ u hκ hs hp).trans
    (pointMeasure_gaussian_strong_sobolev_squared_norm hγ ha hQ hP y hPI f hf hR)
  have h := mul_le_mul_of_nonneg_left hvar (show 0 ≤ M from ENNReal.toReal_nonneg)
  have hv : M * (⨍ x, ‖u x‖ ^ 2 ∂μ) = ∫ x in ball (0 : ℂ) R, ‖u x‖ ^ 2 ∂pointMeasure γ a y := by
    simpa only [smul_eq_mul] using measure_smul_setAverage (μ := pointMeasure γ a y)
      (fun x => ‖u x‖ ^ 2) (s := ball (0 : ℂ) R) (measure_ne_top _ _)
  rw [hv] at h
  have hN : 0 < N := ENNReal.toReal_pos
    (pointMeasure_origin_ball_pos hγ ha y (show 0 < 11 * R by positivity)).ne' (measure_ne_top _ _)
  have hMN : M / N ≤ 1 := (div_le_one hN).mpr
    (measureReal_mono (ball_subset_ball (by linarith)))
  have he : (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) = I / N := by
    rw [setAverage_eq, smul_eq_mul]
    change N⁻¹ * I = I / N
    ring
  rw [he] at h
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (pointGaussianSobolevFactor_pos Q hP).le (Real.exp_pos _).le) (sq_nonneg R)
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg _)
  apply h.trans
  change M * (A * (I / N)) ≤ A * I
  calc
    _ = A * (M / N) * I := by ring
    _ ≤ A * 1 * I := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMN hA) hI
    _ = _ := by ring

end RepulsiveCoulomb
