import LeanResearch.RepulsiveCoulomb.PointGaussianBallComparison
import LeanResearch.RepulsiveCoulomb.MeasureAverageComparisonReverse

/-! Actual normalized restrictions of the Gaussian point measure and raw
product measure are comparable. The partition function cancels exactly. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointMeasure_continuous_ball_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    IntegrableOn f (ball c R) (pointMeasure γ a y) := by
  letI := pointMeasure_isProbability hγ ha y
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall

theorem gaussian_normalization_ratio {Z γ R : ℝ} (hZ : 0 < Z) :
    Z⁻¹ / (Z⁻¹ * Real.exp (-γ * R ^ 2 / 2)) = Real.exp (γ * R ^ 2 / 2) := by
  rw [show -γ * R ^ 2 / 2 = -(γ * R ^ 2 / 2) by ring, Real.exp_neg]
  field_simp

theorem pointMeasure_raw_average_comparison {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R : ℝ} (hR : 0 < R) (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ x, 0 ≤ g x) :
    (⨍ x in ball (0 : ℂ) R, g x ∂pointMeasure γ a y) ≤
      Real.exp (γ * R ^ 2 / 2) * (⨍ x in ball (0 : ℂ) R, g x ∂rawPointMeasure a y) ∧
    (⨍ x in ball (0 : ℂ) R, g x ∂rawPointMeasure a y) ≤
      Real.exp (γ * R ^ 2 / 2) * (⨍ x in ball (0 : ℂ) R, g x ∂pointMeasure γ a y) := by
  let μ := (rawPointMeasure a y).restrict (ball (0 : ℂ) R)
  let ν := (pointMeasure γ a y).restrict (ball (0 : ℂ) R)
  letI := pointMeasure_isProbability hγ ha y
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using rawPointMeasure_ball_lt_top ha y 0 R⟩
  letI : IsFiniteMeasure ν := inferInstance
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (rawPointMeasure_ball_pos ha y 0 hR).ne' (by simpa [μ] using he)⟩
  letI : NeZero ν := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (pointMeasure_origin_ball_pos hγ ha y hR).ne' (by simpa [ν] using he)⟩
  have hZ := pointWeight_integral_pos hγ ha y
  obtain ⟨hlo, hup⟩ := pointMeasure_gaussian_ball_comparison hγ ha y hR.le
  have h := averages_comparable_of_measure_comparison μ ν
    (mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)) (inv_pos.mpr hZ) hlo hup
    (rawPointMeasure_continuous_ball_integrable ha y hg 0 R)
    (pointMeasure_continuous_ball_integrable hγ ha y hg 0 R) hgn
  rwa [gaussian_normalization_ratio hZ] at h

end RepulsiveCoulomb
