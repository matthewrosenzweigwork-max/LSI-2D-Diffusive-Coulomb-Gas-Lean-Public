module

public import LeanResearch.RepulsiveCoulomb.PointMetricMapDifferential
public import LeanResearch.RepulsiveCoulomb.ComplexLinearJacobianBounds

@[expose] public section

/-! Literal absolute-Jacobian and analytic distortion bounds extracted from
an actual point-metric bi-Lipschitz map. Map existence is intentionally separate.
The absolute value accommodates either orientation of a plane homeomorphism. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

theorem pointMetricMap_ae_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {L : ℝ} (hL : 1 ≤ L)
    (hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z))
    (hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / L ^ 2 ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 4 * |(fderiv ℝ F z).toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  filter_upwards [pointMetricMap_ae_differentiableAt ha y hLp.le hupper] with z hz
  have hd (v : ℂ) := pointMetricMap_fderiv_bounds ha y hLp hlower hupper hz v
  have hJ := complex_continuousLinear_jacobian_bounds (fderiv ℝ F z)
    (pointConformalDensity_nonneg a y z) hL (fun v ↦ (hd v).1) (fun v ↦ (hd v).2)
  simp only [div_pow, mul_pow, pointConformalDensity_sq] at hJ
  exact ⟨hz, hJ⟩

/-- The source-style two-sided metric inequalities give the literal weight
comparison with constant L² and analytic outer distortion at most L⁴. -/
theorem pointMetricHomeomorph_ae_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / L ^ 2 ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 4 * |(fderiv ℝ F z).toLinearMap.det| := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply pointMetricMap_ae_jacobian_bounds ha y hL
  · intro p z
    have h := mul_le_mul_of_nonneg_left (hmetric p z).1 hLp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hLp.ne', one_mul, dist_eq_norm] using h
  · intro p z
    simpa only [dist_eq_norm] using (hmetric p z).2

/-- Substituting the sharp Bonk--Lang metric constant gives C=1+q/2 and
K=(1+q/2)² for the extracted absolute Jacobian and outer distortion. This theorem
does not postulate or assert existence of the required metric homeomorphism. -/
theorem pointSharpMetricHomeomorph_ae_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hmetric : ∀ p z,
      (Real.sqrt (1 + q / 2))⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ Real.sqrt (1 + q / 2) * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      rawPointWeight a y z / (1 + q / 2) ≤ |(fderiv ℝ F z).toLinearMap.det| ∧
      |(fderiv ℝ F z).toLinearMap.det| ≤ (1 + q / 2) * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ (1 + q / 2) ^ 2 * |(fderiv ℝ F z).toLinearMap.det| := by
  have hc : 0 ≤ 1 + q / 2 := by positivity
  have hL : 1 ≤ Real.sqrt (1 + q / 2) := by
    rw [Real.le_sqrt (by norm_num) hc]
    nlinarith
  have hL2 := Real.sq_sqrt hc
  have hL4 : Real.sqrt (1 + q / 2) ^ 4 = (1 + q / 2) ^ 2 := by
    calc
      _ = (Real.sqrt (1 + q / 2) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hL2]
  simpa only [hL2, hL4] using pointMetricHomeomorph_ae_jacobian_bounds ha y F hL hmetric

end RepulsiveCoulomb
