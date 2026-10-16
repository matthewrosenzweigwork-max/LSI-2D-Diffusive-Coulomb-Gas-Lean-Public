module

public import LeanResearch.RepulsiveCoulomb.PointMeasureAverage
public import LeanResearch.RepulsiveCoulomb.MeasureAverageComparison

@[expose] public section

/-! Literal Gaussian-vs-raw comparison on origin-centered balls, including
positive punctures. Constants are explicit; normalization cancellation follows
at the normalized-average step. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointDensity_gaussian_ball_bounds {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    ((∫ x : ℂ, pointWeight γ a y x)⁻¹ * Real.exp (-γ * R ^ 2 / 2)) * rawPointWeight a y z ≤
      pointDensity γ a y z ∧
    pointDensity γ a y z ≤ (∫ x : ℂ, pointWeight γ a y x)⁻¹ * rawPointWeight a y z := by
  have hn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hs : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
  have hlo : Real.exp (-γ * R ^ 2 / 2) ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hup : Real.exp (-γ * ‖z‖ ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖])
  have hZ : 0 ≤ (∫ x : ℂ, pointWeight γ a y x)⁻¹ := (inv_pos.mpr (pointWeight_integral_pos hγ ha y)).le
  have hw := rawPointWeight_nonneg a y z
  change _ ≤ (∫ x : ℂ, pointWeight γ a y x)⁻¹ *
    (Real.exp (-γ * ‖z‖ ^ 2 / 2) * rawPointWeight a y z) ∧ _
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlo hw) hZ
  · change (∫ x : ℂ, pointWeight γ a y x)⁻¹ *
      (Real.exp (-γ * ‖z‖ ^ 2 / 2) * rawPointWeight a y z) ≤ _
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hup hw) hZ
    simpa only [one_mul] using h

theorem pointMeasure_gaussian_ball_comparison {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((∫ x : ℂ, pointWeight γ a y x)⁻¹ * Real.exp (-γ * R ^ 2 / 2)) •
      (rawPointMeasure a y).restrict (ball (0 : ℂ) R) ≤ (pointMeasure γ a y).restrict (ball (0 : ℂ) R) ∧
    (pointMeasure γ a y).restrict (ball (0 : ℂ) R) ≤
      ENNReal.ofReal ((∫ x : ℂ, pointWeight γ a y x)⁻¹) • (rawPointMeasure a y).restrict (ball (0 : ℂ) R) := by
  have hZ : 0 ≤ (∫ x : ℂ, pointWeight γ a y x)⁻¹ := (inv_pos.mpr (pointWeight_integral_pos hγ ha y)).le
  have hw := (rawPointWeight_continuous ha y).measurable.ennreal_ofReal
  constructor
  · rw [pointMeasure_eq_withDensity hγ ha y, rawPointMeasure,
      restrict_withDensity measurableSet_ball, restrict_withDensity measurableSet_ball,
      ← withDensity_smul _ hw]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    change ENNReal.ofReal _ * ENNReal.ofReal _ ≤ ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul (mul_nonneg hZ (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (pointDensity_gaussian_ball_bounds hγ ha y hR (ball_subset_closedBall hz)).1
  · rw [pointMeasure_eq_withDensity hγ ha y, rawPointMeasure,
      restrict_withDensity measurableSet_ball, restrict_withDensity measurableSet_ball,
      ← withDensity_smul _ hw]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul hZ]
    exact ENNReal.ofReal_le_ofReal (pointDensity_gaussian_ball_bounds hγ ha y hR (ball_subset_closedBall hz)).2

theorem pointMeasure_origin_ball_pos {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {R : ℝ} (hR : 0 < R) :
    0 < pointMeasure γ a y (ball (0 : ℂ) R) := by
  have h := (pointMeasure_gaussian_ball_comparison hγ ha y hR.le).1 univ
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul] at h
  exact (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (mul_pos (inv_pos.mpr (pointWeight_integral_pos hγ ha y))
    (Real.exp_pos _)), rawPointMeasure_ball_pos ha y 0 hR⟩).trans_le h

end RepulsiveCoulomb
